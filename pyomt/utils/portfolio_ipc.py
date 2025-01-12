# Standard library imports
import enum
import json
import sys
import threading
import time
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Union

# Multiprocessing imports
import multiprocessing as mp
from multiprocessing import Event, Pipe, Process, Queue, get_context
from multiprocessing.connection import Connection

# System/OS related imports
import psutil
import signal


class PortfolioException(Exception):
    """Base exception for portfolio solver errors"""
    pass


class TimeoutException(PortfolioException):
    """Raised when portfolio solver times out"""
    pass


class MessageType(enum.Enum):
    STATUS = "status"
    PROGRESS = "progress"
    INTERMEDIATE_RESULT = "intermediate_result"
    RESOURCE_USAGE = "resource_usage"
    ERROR = "error"
    CONTROL = "control"


@dataclass
class Message:
    type: MessageType
    data: Any
    timestamp: float = None
    worker_id: int = None

    def __post_init__(self):
        if self.timestamp is None:
            self.timestamp = time.time()

    def to_dict(self):
        return {
            "type": self.type.value,
            "data": self.data,
            "timestamp": self.timestamp,
            "worker_id": self.worker_id
        }

    @classmethod
    def from_dict(cls, d):
        return cls(
            type=MessageType(d["type"]),
            data=d["data"],
            timestamp=d["timestamp"],
            worker_id=d["worker_id"]
        )


class WorkerStatus(enum.Enum):
    INITIALIZING = "initializing"
    RUNNING = "running"
    PAUSED = "paused"
    COMPLETED = "completed"
    ERROR = "error"


class ControlCommand(enum.Enum):
    PAUSE = "pause"
    RESUME = "resume"
    STOP = "stop"
    REQUEST_STATUS = "request_status"


def terminate_process_tree(pid: int) -> None:
    """Recursively terminate a process and all its children"""
    try:
        parent = psutil.Process(pid)
        children = parent.children(recursive=True)

        for child in children:
            try:
                child.terminate()
            except psutil.NoSuchProcess:
                pass

        try:
            parent.terminate()
        except psutil.NoSuchProcess:
            pass

        gone, alive = psutil.wait_procs(children + [parent], timeout=3)
        for p in alive:
            try:
                p.kill()
            except psutil.NoSuchProcess:
                pass

    except psutil.NoSuchProcess:
        pass


def worker_wrapper(func: Callable, args: tuple, worker_id: int,
                   result_queue: Queue, error_queue: Queue,
                   comm_pipe: Connection, control_event: Event,
                   status_interval: float = 1.0) -> None:
    """Enhanced worker wrapper with communication support"""

    def send_message(msg_type: MessageType, data: Any):
        msg = Message(type=msg_type, data=data, worker_id=worker_id)
        comm_pipe.send(msg.to_dict())

    def handle_control_commands():
        if comm_pipe.poll():
            msg_dict = comm_pipe.recv()
            msg = Message.from_dict(msg_dict)
            if msg.type == MessageType.CONTROL:
                cmd = ControlCommand(msg.data)
                if cmd == ControlCommand.PAUSE:
                    control_event.clear()
                elif cmd == ControlCommand.RESUME:
                    control_event.set()
                elif cmd == ControlCommand.STOP:
                    raise InterruptedError("Worker stopped by control command")
                elif cmd == ControlCommand.REQUEST_STATUS:
                    send_status()

    def send_status():
        process = psutil.Process()
        status_data = {
            "cpu_percent": process.cpu_percent(),
            "memory_percent": process.memory_percent(),
            "status": current_status.value
        }
        send_message(MessageType.STATUS, status_data)

    try:
        current_status = WorkerStatus.INITIALIZING
        # Send status as dictionary instead of just the value
        send_message(MessageType.STATUS, {"status": current_status.value})

        # Start status monitoring thread
        def status_monitor():
            while True:
                if stop_monitor.is_set():
                    break
                send_status()
                time.sleep(status_interval)

        stop_monitor = threading.Event()
        monitor_thread = threading.Thread(target=status_monitor)
        monitor_thread.start()

        # Main worker logic
        current_status = WorkerStatus.RUNNING
        # Send status as dictionary instead of just the value
        send_message(MessageType.STATUS, {"status": current_status.value})

        result = None
        try:
            while True:
                handle_control_commands()

                # Wait for resume if paused
                control_event.wait()

                # Actual computation step
                if result is None:
                    result = func(*args)
                    send_message(MessageType.INTERMEDIATE_RESULT, result)
                else:
                    break

        finally:
            # Clean up status monitor
            stop_monitor.set()
            monitor_thread.join()

        current_status = WorkerStatus.COMPLETED
        # Send status as dictionary instead of just the value
        send_message(MessageType.STATUS, {"status": current_status.value})
        result_queue.put(result)

    except Exception as e:
        current_status = WorkerStatus.ERROR
        # Send status as dictionary instead of just the value
        send_message(MessageType.STATUS, {
            "status": current_status.value,
            "error": str(e)
        })
        send_message(MessageType.ERROR, str(e))
        error_queue.put((type(e), str(e), sys.exc_info()[2]))


class Portfolio:
    def __init__(self, timeout: float = 60, start_method: str = None,
                 status_interval: float = 1.0):
        self.timeout = timeout
        self.status_interval = status_interval
        self._processes: List[Process] = []
        self._pipes: List[Connection] = []
        self._control_events: List[Event] = []
        self._ctx = get_context(start_method) if start_method else mp.get_context()

        # Message handlers
        self._message_handlers = {
            MessageType.STATUS: self._handle_status,
            MessageType.PROGRESS: self._handle_progress,
            MessageType.INTERMEDIATE_RESULT: self._handle_intermediate_result,
            MessageType.RESOURCE_USAGE: self._handle_resource_usage,
            MessageType.ERROR: self._handle_error
        }

        # State tracking
        self._worker_states: Dict[int, Dict] = {}
        self._intermediate_results: Dict[int, List] = {}

    def _handle_status(self, msg: Message):
        """Handle status messages from workers"""
        worker_id = msg.worker_id
        if worker_id not in self._worker_states:
            self._worker_states[worker_id] = {}

        # msg.data is now guaranteed to be a dictionary
        self._worker_states[worker_id].update(msg.data)

    def _handle_progress(self, msg: Message):
        worker_id = msg.worker_id
        if worker_id not in self._worker_states:
            self._worker_states[worker_id] = {}
        self._worker_states[worker_id]['progress'] = msg.data

    def _handle_intermediate_result(self, msg: Message):
        worker_id = msg.worker_id
        if worker_id not in self._intermediate_results:
            self._intermediate_results[worker_id] = []
        self._intermediate_results[worker_id].append(msg.data)

    def _handle_resource_usage(self, msg: Message):
        worker_id = msg.worker_id
        if worker_id not in self._worker_states:
            self._worker_states[worker_id] = {}
        self._worker_states[worker_id]['resources'] = msg.data

    def _handle_error(self, msg: Message):
        worker_id = msg.worker_id
        if worker_id not in self._worker_states:
            self._worker_states[worker_id] = {}
        self._worker_states[worker_id]['error'] = msg.data

    def get_worker_state(self, worker_id: int) -> Dict:
        """Get current state of a specific worker"""
        return self._worker_states.get(worker_id, {})

    def get_all_states(self) -> Dict[int, Dict]:
        """Get current states of all workers"""
        return self._worker_states.copy()

    def get_intermediate_results(self, worker_id: int) -> List:
        """Get intermediate results from a specific worker"""
        return self._intermediate_results.get(worker_id, [])

    def send_control_command(self, worker_id: int, command: ControlCommand):
        """Send control command to a specific worker"""
        if 0 <= worker_id < len(self._pipes):
            msg = Message(
                type=MessageType.CONTROL,
                data=command.value,
                worker_id=worker_id
            )
            self._pipes[worker_id][0].send(msg.to_dict())

    def pause_worker(self, worker_id: int):
        """Pause a specific worker"""
        self.send_control_command(worker_id, ControlCommand.PAUSE)

    def resume_worker(self, worker_id: int):
        """Resume a specific worker"""
        self.send_control_command(worker_id, ControlCommand.RESUME)

    def stop_worker(self, worker_id: int):
        """Stop a specific worker"""
        self.send_control_command(worker_id, ControlCommand.STOP)

    def solve(self, solvers: List[Callable], args: tuple) -> Any:
        """Enhanced solve method with communication support"""
        result_queue = self._ctx.Queue()
        error_queue = self._ctx.Queue()

        # Create communication pipes and control events for each worker
        for i in range(len(solvers)):
            parent_conn, child_conn = self._ctx.Pipe()
            self._pipes.append((parent_conn, child_conn))
            self._control_events.append(self._ctx.Event())
            self._control_events[-1].set()  # Start in running state

        # Start all worker processes
        for i, solver in enumerate(solvers):
            p = self._ctx.Process(
                target=worker_wrapper,
                args=(solver, args, i, result_queue, error_queue,
                      self._pipes[i][1], self._control_events[i],
                      self.status_interval)
            )
            self._processes.append(p)
            p.start()

        try:
            start_time = time.time()
            while True:
                # Handle communication from workers
                for i, (parent_conn, _) in enumerate(self._pipes):
                    if parent_conn.poll():
                        msg_dict = parent_conn.recv()
                        msg = Message.from_dict(msg_dict)
                        handler = self._message_handlers.get(msg.type)
                        if handler:
                            handler(msg)

                # Check for results
                try:
                    result = result_queue.get_nowait()
                    return result
                except mp.queues.Empty:
                    pass

                # Check for errors
                try:
                    exc_type, exc_msg, exc_tb = error_queue.get_nowait()
                    raise exc_type(exc_msg)
                except mp.queues.Empty:
                    pass

                # Check timeout
                if time.time() - start_time > self.timeout:
                    raise TimeoutException("Portfolio solver timed out")

                time.sleep(0.01)

        finally:
            # Clean up
            for p in self._processes:
                if p.is_alive():
                    terminate_process_tree(p.pid)
            self._processes.clear()
            self._pipes.clear()
            self._control_events.clear()
            self._worker_states.clear()
            self._intermediate_results.clear()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        for p in self._processes:
            if p.is_alive():
                terminate_process_tree(p.pid)
        self._processes.clear()
        self._pipes.clear()
        self._control_events.clear()
        self._worker_states.clear()
        self._intermediate_results.clear()
