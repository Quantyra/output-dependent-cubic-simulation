"""Compare observed GCP warning headers with an explicitly partial baseline.

This summarizes logs; it does not establish a complete warning baseline or a
successful Lean build. Cached modules may not replay warning output.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def headers(text):
    return [line for line in text.splitlines() if line.startswith("warning: SectorSimulation/")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--partial-headers", required=True, type=Path)
    parser.add_argument("logs", nargs="+", type=Path)
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text(encoding="utf-8"))
    raw = args.partial_headers.read_bytes()
    if hashlib.sha256(raw).hexdigest() != inventory["headers_sha256"]:
        raise SystemExit("partial warning header hash mismatch")
    baseline = Counter(headers(raw.decode("utf-8")))
    if sum(baseline.values()) != inventory["header_count"]:
        raise SystemExit("partial warning header count mismatch")
    observed = Counter()
    log_hashes = {}
    for path in args.logs:
        content = path.read_bytes()
        log_hashes[str(path)] = hashlib.sha256(content).hexdigest()
        observed |= Counter(headers(content.decode("utf-8", errors="replace")))
    def entries(counter):
        return [{"header": key, "count": count} for key, count in sorted(counter.items())]
    result = {
        "scope": "Observed log headers compared with an incomplete baseline; absence is not proof of no warning, and not-in-partial does not mean new.",
        "source_commit": inventory["source_commit"],
        "partial_baseline_headers": sum(baseline.values()),
        "observed_headers": sum(observed.values()),
        "observed_in_both": sum((baseline & observed).values()),
        "baseline_not_observed": entries(baseline - observed),
        "observed_not_in_partial": entries(observed - baseline),
        "log_sha256": log_hashes,
    }
    print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
