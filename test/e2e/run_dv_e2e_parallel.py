#!/usr/bin/env python3
import os
import sys
import re
import subprocess
import shutil
import tempfile
import multiprocessing
import time

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
SISAL = os.path.join(REPO, "_build/install/default/bin/sisal")
RUNTIME = os.path.join(REPO, "runtime")
HARNESS = os.path.join(REPO, "test/e2e/dv_run_all.cpp")
NUMPY_VERIFY = os.path.join(REPO, "test/e2e/numpy_verify.cpp")
E2E_SH = os.path.join(REPO, "test/e2e/run_dv_e2e.sh")

CXX_BASE = [
    "clang++", "-std=c++17", f"-I{RUNTIME}",
    "-framework", "Accelerate", "-DACCELERATE_NEW_LAPACK"
]

def parse_test_groups():
    groups = []
    with open(E2E_SH, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            # Match run_group MACRO stem [flags]
            match = re.match(r'^run_group\s+([A-Za-z0-9_]+)\s+([A-Za-z0-9_]+)(?:\s+(.*))?$', line)
            if match:
                macro = match.group(1)
                stem = match.group(2)
                flags_raw = match.group(3) or ""
                # Clean up flags
                flags = flags_raw.strip().strip('"').strip("'").strip()
                groups.append((macro, stem, flags))
    return groups

def run_single_test(args):
    macro, stem, flags, gendir = args
    cpp_out = os.path.join(gendir, f"{stem}.cpp")
    bin_out = os.path.join(gendir, f"test_{macro}")

    # 1. Emit C++
    cmd_emit = [SISAL, os.path.join(REPO, f"test/e2e/{stem}.sis")]
    if flags:
        cmd_emit.extend(flags.split())
    cmd_emit.append(f"--c={cpp_out}")

    res_emit = subprocess.run(cmd_emit, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if res_emit.returncode != 0:
        return macro, False, "EMIT", res_emit.stdout + res_emit.stderr

    # 2. Compile and Link C++
    cmd_build = CXX_BASE + [
        f"-DTEST_{macro}", HARNESS, NUMPY_VERIFY, cpp_out, "-o", bin_out
    ]
    res_build = subprocess.run(cmd_build, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if res_build.returncode != 0:
        return macro, False, "BUILD", res_build.stdout + res_build.stderr

    # 3. Run test binary
    res_run = subprocess.run([bin_out], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if res_run.returncode != 0:
        return macro, False, "RUN", res_run.stdout + res_run.stderr

    return macro, True, "PASS", res_run.stdout

def main():
    print("=== Building compiler ===")
    res = subprocess.run(["dune", "build"], cwd=REPO)
    if res.returncode != 0:
        print("Compiler build failed!")
        sys.exit(1)
    
    res = subprocess.run(["dune", "build", "@install"], cwd=REPO)
    if res.returncode != 0:
        print("Compiler install build failed!")
        sys.exit(1)

    groups = parse_test_groups()
    print(f"Found {len(groups)} test groups to run.")

    gendir = tempfile.mkdtemp(prefix="sisal_e2e_parallel_")
    
    # Prepare multiprocessing arguments
    pool_args = [(macro, stem, flags, gendir) for macro, stem, flags in groups]
    num_workers = multiprocessing.cpu_count()
    print(f"Running tests in parallel using {num_workers} workers...")

    start_time = time.time()
    
    passed_count = 0
    failed_count = 0
    failures = []

    with multiprocessing.Pool(processes=num_workers) as pool:
        # Use imap_unordered for streaming results
        for macro, success, stage, log in pool.imap_unordered(run_single_test, pool_args):
            if success:
                passed_count += 1
                print(f"\033[32m[PASS]\033[0m {macro:<40}")
            else:
                failed_count += 1
                failures.append((macro, stage, log))
                print(f"\033[31m[FAIL]\033[0m {macro:<40} (Stage: {stage})")

    elapsed = time.time() - start_time
    print(f"\nCompleted in {elapsed:.2f} seconds.")

    # Cleanup temp directory
    shutil.rmtree(gendir, ignore_errors=True)

    if failures:
        print("\n=== FAILURE DETAILS ===")
        for macro, stage, log in failures:
            print(f"\n----------------------------------------")
            print(f"FAIL: {macro} (Stage: {stage})")
            print(f"----------------------------------------")
            print(log)

    print("\n========================================")
    print(f"Groups passed: {passed_count}  Groups with failures: {failed_count}")
    print("========================================")

    if failed_count > 0:
        sys.exit(1)
    else:
        sys.exit(0)

if __name__ == "__main__":
    main()
