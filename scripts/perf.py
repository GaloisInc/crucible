#!/usr/bin/env python3
"""Collect and analyze deterministic performance metrics from GHC RTS output."""

from dataclasses import dataclass
from typing import Optional
import re
import subprocess
import sys
from argparse import ArgumentParser


@dataclass
class RTSStats:
    """GHC RTS statistics from -s output."""

    bytes_allocated: int
    bytes_copied: int
    max_residency: int
    max_slop: int
    total_memory_mb: float
    gen0_collections: int
    gen1_collections: int
    productivity_percent: float

    def format_markdown_table(self) -> str:
        """Format stats as markdown tables."""
        memory_table = f"""### Memory Allocation

| Metric | Value |
|--------|-------|
| Bytes Allocated | {self.bytes_allocated:,} |
| Max Residency | {self.max_residency:,} |
| Bytes Copied (GC) | {self.bytes_copied:,} |
| Max Slop | {self.max_slop:,} |
| Total Memory (MB) | {self.total_memory_mb:.1f} |
| Productivity | {self.productivity_percent:.1f}% |
"""

        gc_table = f"""### GC Statistics

| Metric | Value |
|--------|-------|
| Gen 0 Collections | {self.gen0_collections} |
| Gen 1 Collections | {self.gen1_collections} |
"""

        return memory_table + "\n" + gc_table


@dataclass
class PerfMetrics:
    """Complete performance metrics for a test run."""

    package: str
    cli_args: list[str]
    rts_stats: RTSStats
    git_ref: str
    commit_sha: str
    raw_rts_output: str

    @classmethod
    def from_rts_output(
        cls,
        stderr: str,
        package: str,
        cli_args: list[str],
        ref: str,
        commit_sha: str,
    ) -> "PerfMetrics":
        """Parse RTS output and create metrics object."""
        stats = parse_rts_output(stderr)
        return cls(
            package=package,
            cli_args=cli_args,
            rts_stats=stats,
            git_ref=ref,
            commit_sha=commit_sha,
            raw_rts_output=stderr,
        )


def parse_rts_output(stderr: str) -> RTSStats:
    """Parse GHC RTS -s output to extract deterministic metrics."""
    bytes_allocated_match = re.search(r"([\d,]+) bytes allocated in the heap", stderr)
    bytes_copied_match = re.search(r"([\d,]+) bytes copied during GC", stderr)
    max_residency_match = re.search(r"([\d,]+) bytes maximum residency", stderr)
    max_slop_match = re.search(r"([\d,]+) bytes maximum slop", stderr)
    total_memory_match = re.search(r"(\d+) MiB total memory in use", stderr)
    gen0_match = re.search(r"Gen\s+0\s+(\d+) colls", stderr)
    gen1_match = re.search(r"Gen\s+1\s+(\d+) colls", stderr)
    productivity_match = re.search(r"Productivity\s+([\d.]+)%", stderr)

    def parse_number(match: Optional[re.Match]) -> int:
        if match is None:
            return 0
        return int(match.group(1).replace(",", ""))

    def parse_float(match: Optional[re.Match]) -> float:
        if match is None:
            return 0.0
        return float(match.group(1))

    return RTSStats(
        bytes_allocated=parse_number(bytes_allocated_match),
        bytes_copied=parse_number(bytes_copied_match),
        max_residency=parse_number(max_residency_match),
        max_slop=parse_number(max_slop_match),
        total_memory_mb=parse_float(total_memory_match),
        gen0_collections=parse_number(gen0_match),
        gen1_collections=parse_number(gen1_match),
        productivity_percent=parse_float(productivity_match),
    )


def get_commit_sha() -> str:
    """Get short commit SHA (7 characters)."""
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"],
        text=True,
        stderr=subprocess.DEVNULL,
    ).strip()[:7]


def get_current_commit_info() -> tuple[str, str]:
    """Get current git ref and commit SHA."""
    try:
        ref = subprocess.check_output(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except subprocess.CalledProcessError:
        ref = "HEAD"

    return ref, get_commit_sha()


def checkout_ref(ref: Optional[str]) -> tuple[str, str]:
    """Checkout a git ref if specified, otherwise use current HEAD."""
    if ref is None:
        return get_current_commit_info()

    print(f"Checking out ref: {ref}", file=sys.stderr)
    subprocess.check_call(
        ["git", "checkout", ref],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    return ref, get_commit_sha()


def run_with_cabal(package: str, args: list[str]) -> str:
    """Run crux-llvm with cabal, adding RTS flags."""
    cmd = ["cabal", "run", package, "--"] + args + ["+RTS", "-s"]

    print(f"Running: {' '.join(cmd)}", file=sys.stderr)

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
    )

    # crux-llvm may exit non-zero when it finds counterexamples; capture stderr
    # regardless of exit code so RTS stats are always available.
    return result.stderr


def format_markdown(metrics: PerfMetrics) -> str:
    """Format metrics as markdown for GitHub job summary."""
    cmd_str = f"cabal run {metrics.package} -- {' '.join(metrics.cli_args)} +RTS -s"

    markdown = f"""## Performance Metrics

**Package:** `{metrics.package}`
**Command:** `{cmd_str}`
**Commit:** `{metrics.git_ref}` @ `{metrics.commit_sha}`

{metrics.rts_stats.format_markdown_table()}
<details>
<summary>Raw RTS Output</summary>

```
{metrics.raw_rts_output.strip()}
```
</details>

"""
    return markdown


def main() -> int:
    """Main entry point."""
    parser = ArgumentParser(
        description="Collect deterministic performance metrics from GHC RTS output"
    )
    parser.add_argument(
        "--ref",
        type=str,
        default=None,
        help="Git ref to checkout (branch, tag, commit SHA). If not specified, uses current HEAD.",
    )
    parser.add_argument(
        "--package",
        type=str,
        required=True,
        help="Cabal target to run (e.g., exe:crux-llvm)",
    )
    parser.add_argument(
        "args",
        nargs="+",
        help="Arguments to pass to crux-llvm",
    )

    args = parser.parse_args()

    ref, commit_sha = checkout_ref(args.ref)
    stderr = run_with_cabal(args.package, args.args)
    metrics = PerfMetrics.from_rts_output(
        stderr, args.package, args.args, ref, commit_sha
    )

    print(format_markdown(metrics))

    return 0


if __name__ == "__main__":
    sys.exit(main())
