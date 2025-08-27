"""
Download pre-built SMT solvers and rename the binary solvers as 
cvc5 and z3
"""
import os
import platform
import re
import shutil
import sys
import tarfile
import zipfile

import urllib.request
import urllib.error

# yices2_mac_arm64 = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-arm-apple-darwin20.6.0.tar.gz"
# yices2_mac = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-apple-darwin20.6.0.tar.gz"
# yices2_win64 = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-unknown-mingw32-static-gmp.zip"
# yices2_linux = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-pc-linux-gnu.tar.gz"


SOLVER_URLS = {
    'mac_arm64': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS-arm64",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-arm64-osx-11.0.zip",
    },
    'mac_x64': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-osx-10.16.zip",
    },
    'linux': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Linux",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-glibc-2.31.zip",
    }
}


def get_binary_path(solver_name, archive_name):
    if solver_name == 'cvc5':
        return archive_name
    elif solver_name == 'z3':
        match = re.search(r'(z3-\d+\.\d+\.\d+-[^.]+\.\d+)', archive_name)
        if match:
            base_name = match.group(1)
            return f'{base_name}/bin/z3'
    return None


def get_os_type():
    system = platform.system().lower()
    if system == 'darwin':
        machine = platform.machine()
        if machine == 'arm64':
            return 'mac_arm64'
        return 'mac_x64'
    elif system == 'linux':
        return 'linux'
    return None


def download_file(url, output_file=None):
    if output_file is None:
        output_file = url.split('/')[-1]

    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req) as response, open(output_file, 'wb') as f:
            print(f"Downloading {os.path.basename(output_file)}...")
            shutil.copyfileobj(response, f)
        return output_file
    except (urllib.error.URLError, OSError) as e:
        print(f"Failed to download: {url}")
        print(f"Error: {e}")
        return None


def extract_archive(filename):
    try:
        print(f"Extracting {os.path.basename(filename)}...")
        if filename.endswith('.zip'):
            with zipfile.ZipFile(filename, 'r') as zip_ref:
                zip_ref.extractall()
        elif filename.endswith('.tar.gz'):
            with tarfile.open(filename, 'r:gz') as tar_ref:
                tar_ref.extractall()
        return True
    except Exception as e:
        print(f"Failed to extract {filename}: {e}")
        return False


def find_binary(solver_name, archive_name):
    if solver_name == 'cvc5':
        return archive_name
    if archive_name.endswith(('.zip', '.tar.gz')):
        binary_path = get_binary_path(solver_name, archive_name)
        if binary_path and os.path.exists(binary_path):
            return binary_path
    return None


def get_extracted_dir(solver_name, archive_name):
    if solver_name == 'z3':
        match = re.search(r'(z3-\d+\.\d+\.\d+-.*?)(\.zip|\.tar\.gz)', archive_name)
        if match:
            return match.group(1)
    return archive_name.replace('.zip', '').replace('.tar.gz', '')


def setup_solvers():
    os_type = get_os_type()
    if os_type not in SOLVER_URLS:
        print(f"Unsupported OS: {platform.system()}")
        return False

    success = True
    print(f"Setting up solvers for {os_type}")

    for solver_name, url in SOLVER_URLS[os_type].items():
        target_path = os.path.join('.', solver_name)
        if os.path.exists(target_path):
            print(f"✓ {solver_name} already exists, skipping")
            continue

        print(f"\nSetting up {solver_name}...")
        downloaded_file = download_file(url)
        if not downloaded_file:
            success = False
            continue

        if downloaded_file.endswith(('.zip', '.tar.gz')):
            if not extract_archive(downloaded_file):
                success = False
                continue

        binary_path = find_binary(solver_name, downloaded_file)
        if binary_path and os.path.exists(binary_path):
            shutil.copy2(binary_path, solver_name)
            os.chmod(solver_name, 0o755)
            print(f"✓ {solver_name} setup complete")
        else:
            print(f"✗ Failed to setup {solver_name}")
            success = False

        # Cleanup
        if downloaded_file.endswith(('.zip', '.tar.gz')):
            os.remove(downloaded_file)
            extracted_dir = get_extracted_dir(solver_name, downloaded_file)
            if os.path.exists(extracted_dir):
                shutil.rmtree(extracted_dir)
        else:
            os.remove(downloaded_file)

    return success


if __name__ == '__main__':
    try:
        if setup_solvers():
            print("✓ All solvers setup complete")
        else:
            print("✗ Setup failed")
    except KeyboardInterrupt:
        print("\nSetup interrupted")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)
