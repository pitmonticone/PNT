#!/usr/bin/env python3
"""Submit parallel Aristotle proof jobs for each sorry in a Lean 4 file.

For each `sorry` in the input file, this script creates a temporary copy where
that sorry is preserved and all others are replaced with `admit`, then submits
each copy to the Aristotle API as a separate proof job.

Requirements:
    pip install aristotlelib

Authentication:
    Provide your Aristotle API key in one of two ways:
    - Command-line flag:  --key YOUR_API_KEY
    - Environment variable: export ARISTOTLE_API_KEY=YOUR_API_KEY

Usage:
    # Submit jobs for all sorries
    python aristotle_parallel_public.py path/to/file.lean --key YOUR_API_KEY

    # Submit only the first 5 sorries
    python aristotle_parallel_public.py path/to/file.lean -l 5

    # Submit sorries 3 through 7 (1-indexed)
    python aristotle_parallel_public.py path/to/file.lean -r 3-7

    # Submit from sorry 10 to the end
    python aristotle_parallel_public.py path/to/file.lean -r 10-

Temporary files are written to a `tmp/` directory relative to the current
working directory. Each job is submitted sequentially and polled until its
status moves past NOT_STARTED before the next submission begins.
"""

import sys
import os
import re
import tempfile
import asyncio
import argparse
from pathlib import Path

import aristotlelib


async def main():
    parser = argparse.ArgumentParser(
        description="Submit parallel Aristotle jobs, one for each sorry in the input file."
    )
    parser.add_argument("input_file", type=Path, help="Path to the input .lean file")
    parser.add_argument(
        "--key", "-k",
        type=str,
        default=None,
        help="Aristotle API key (default: read from ARISTOTLE_API_KEY environment variable)"
    )
    parser.add_argument(
        "--limit", "-l",
        type=int,
        default=None,
        help="Maximum number of sorries to submit (default: no limit)"
    )
    parser.add_argument(
        "--range", "-r",
        type=str,
        default=None,
        help="Range of sorries to submit (1-indexed), e.g., '1-5', '3-3', '10-' (from 10 to end)"
    )
    args = parser.parse_args()

    # Set API key: prefer --key flag, fall back to environment variable
    api_key = args.key or os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        print("Error: No API key provided. Use --key or set the ARISTOTLE_API_KEY environment variable.", file=sys.stderr)
        sys.exit(1)
    aristotlelib.set_api_key(api_key)

    input_path = args.input_file
    if not input_path.exists():
        print(f"Error: File not found: {input_path}", file=sys.stderr)
        sys.exit(1)

    content = input_path.read_text()

    # Find all matches of \bsorry\b
    sorry_pattern = re.compile(r"\bsorry\b")
    matches = list(sorry_pattern.finditer(content))

    if not matches:
        print("No 'sorry' found in the input file.")
        sys.exit(0)

    print(f"Found {len(matches)} sorry(s) in {input_path}")

    # Keep all matches for replacement logic
    all_matches = matches

    # Parse range if provided
    if args.range:
        range_match = re.match(r"^(\d+)-(\d*)$", args.range)
        if not range_match:
            print(f"Error: Invalid range format '{args.range}'. Use '1-5', '3-3', or '10-'", file=sys.stderr)
            sys.exit(1)
        start = int(range_match.group(1))
        end_str = range_match.group(2)
        end = int(end_str) if end_str else len(matches)

        if start < 1:
            print(f"Error: Range start must be >= 1, got {start}", file=sys.stderr)
            sys.exit(1)
        if end < start:
            print(f"Error: Range end ({end}) must be >= start ({start})", file=sys.stderr)
            sys.exit(1)
        if start > len(matches):
            print(f"Error: Range start ({start}) exceeds number of sorries ({len(matches)})", file=sys.stderr)
            sys.exit(1)

        # Convert to 0-indexed and slice
        end = min(end, len(matches))  # Clamp end to available sorries
        print(f"Selecting sorries {start} to {end} (out of {len(matches)})")
        selected_matches = matches[start - 1 : end]
    elif args.limit is not None:
        # Apply limit if no range specified
        if len(matches) > args.limit:
            print(f"Limiting to first {args.limit} sorries (out of {len(matches)})")
            selected_matches = matches[:args.limit]
        else:
            selected_matches = matches
    else:
        selected_matches = matches

    # Create tmp directory if it doesn't exist
    tmp_dir = Path("tmp")
    tmp_dir.mkdir(exist_ok=True)

    # For each selected sorry, create a tempfile with that sorry preserved and others replaced with admit
    tempfiles = []
    for i, target_match in enumerate(selected_matches):
        # Build new content: replace all sorries except the target one with 'admit'
        new_content_parts = []
        last_end = 0

        for match in all_matches:
            new_content_parts.append(content[last_end : match.start()])
            if match.start() == target_match.start():
                # Keep this sorry
                new_content_parts.append("sorry")
            else:
                # Replace with admit
                new_content_parts.append("admit")
            last_end = match.end()

        new_content_parts.append(content[last_end:])
        new_content = "".join(new_content_parts)

        # Create tempfile in tmp directory
        tmp = tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False, prefix=f"{input_path.stem}_sorry_{i}_", dir=tmp_dir
        )
        tmp.write(new_content)
        tmp.close()
        tempfiles.append(tmp.name)
        print(f"Created tempfile for sorry {i + 1}/{len(selected_matches)}: {tmp.name}")

    # Submit all tempfiles one-by-one (to short-circuit on rate limit failures)
    project_ids = []
    for i, tmpfile in enumerate(tempfiles):
        print(f"Submitting {i + 1}/{len(tempfiles)}: {tmpfile}")
        project_id = await aristotlelib.Project.prove_from_file(
            input_file_path=tmpfile, wait_for_completion=False
        )
        project_ids.append(project_id)
        print(f"  Submitted successfully, project_id: {project_id}")

        # Poll until status moves from NOT_STARTED
        project = await aristotlelib.Project.from_id(project_id)
        while project.status == aristotlelib.ProjectStatus.NOT_STARTED:
            print(f"  Status is NOT_STARTED, waiting...")
            await asyncio.sleep(2)
            await project.refresh()
        print(f"  Status moved to: {project.status}")

    print(f"\nSubmitted {len(project_ids)}/{len(tempfiles)} projects.")
    for i, pid in enumerate(project_ids):
        print(f"  Job {i + 1}: {pid}")


if __name__ == "__main__":
    asyncio.run(main())
