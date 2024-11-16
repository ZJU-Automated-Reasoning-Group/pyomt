# This file was used in the evaluation part of a paper.
# As the development of the code, the dockerfile might be broken.

# syntax=docker/dockerfile:1
FROM ubuntu:22.04
# docker build -t omt:latest .
# docker run -it omt:latest
# change apt source
RUN sed -i s@/archive.ubuntu.com/@/mirrors.zju.edu.cn/@g /etc/apt/sources.list
RUN apt-get clean
RUN apt-get update
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    git \
    vim \
    tmux \
    wget \
    curl \
    # for Yices2
    libgmp-dev\
    swig \
    cmake \
    autoconf \
    gperf \
    libboost-all-dev \
    build-essential \
    default-jre \
    zip


RUN mkdir omt
COPY . /omt

# install efmc package requirements
RUN pip install -r /omt/requirements.txt


# install cudd library
WORKDIR /omt/bin_solvers/
RUN python3 /omt/bin_solvers/download.py
RUN /omt/bin_solvers/download.sh

WORKDIR /