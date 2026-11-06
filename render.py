# /// script
# requires-python = ">=3.12"
# dependencies = ["huggingface-hub==0.34.4", "pyarrow==21.0.0"]
# ///
"""Render pinned Numina proof sources with `uv run render.py`."""

from collections import Counter
import hashlib
import json
from pathlib import Path
from uuid import UUID

from huggingface_hub import hf_hub_download
import pyarrow.parquet as pq

REVISION = "51fa67f1f647ae1ecd81eef9f19306aa8a7b3a94"
SHA256 = "cddeac3b98ad642b53e41b1751ceb7ab34ad22019d8e542b403de67ecf337bc9"


def main():
    root = Path(__file__).resolve().parent
    parquet = Path(
        hf_hub_download(
            "AI-MO/NuminaMath-LEAN",
            "data/train-00000-of-00001.parquet",
            repo_type="dataset",
            revision=REVISION,
        )
    )
    if hashlib.sha256(parquet.read_bytes()).hexdigest() != SHA256:
        raise ValueError("Upstream checksum mismatch")
    counts = Counter()
    seen = set()
    with (root / "index.jsonl").open("w") as index:
        for batch in pq.ParquetFile(parquet).iter_batches(batch_size=64):
            for row in batch.to_pylist():
                identifier = str(UUID(row["uuid"]))
                counts["duplicate_uuid_rows"] += identifier in seen
                seen.add(identifier)
                counts["rows"] += 1
                candidates = []
                if (
                    row["ground_truth_type"] == "complete"
                    and row["formal_ground_truth"]
                ):
                    candidates.append(
                        ("Human", "formal_ground_truth", row["formal_ground_truth"])
                    )
                if row["formal_proof"] and all(
                    row["formal_proof"] != source for _, _, source in candidates
                ):
                    candidates.append(("Model", "formal_proof", row["formal_proof"]))
                counts["rows_with_candidates"] += bool(candidates)
                for origin, field, source in candidates:
                    path = (
                        Path("Numina")
                        / origin
                        / f"R{counts['rows']:06d}_{UUID(identifier).hex}.lean"
                    )
                    (root / path).parent.mkdir(parents=True, exist_ok=True)
                    (root / path).write_bytes(source.encode("utf-8"))
                    counts[origin] += 1
                    index.write(
                        json.dumps(
                            {
                                "uuid": identifier,
                                "row": counts["rows"] - 1,
                                "field": field,
                                "path": path.as_posix(),
                                "module": ".".join(path.with_suffix("").parts),
                                "sha256": hashlib.sha256(
                                    source.encode("utf-8")
                                ).hexdigest(),
                            },
                            sort_keys=True,
                        )
                        + "\n"
                    )
    (root / "provenance.json").write_text(
        json.dumps(
            {
                "dataset": "AI-MO/NuminaMath-LEAN",
                "revision": REVISION,
                "parquet_sha256": SHA256,
                "counts": dict(counts),
                "validation": "Unverified supplied source; not replay-checked records",
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    print(json.dumps(dict(counts), sort_keys=True))


if __name__ == "__main__":
    main()
