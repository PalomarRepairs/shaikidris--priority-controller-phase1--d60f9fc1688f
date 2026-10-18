"""Bind a clean release snapshot to the pinned Palomar input/metadata contract.

Adapted from the author-owned tested guard for GallaiTwoException. This
preparation check does not run Comparator, kernels or any registry action.
"""

import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys


PIPELINE = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
WORKFLOW = ".github/workflows/palomar-rehearsal.yml"
PROFILE = "palomar-standard-v1"


def git(root, *args):
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE
    ).strip()


def require_snapshot(root, commit):
    if Path(git(root, "rev-parse", "--show-toplevel")).resolve() != root.resolve():
        raise ValueError("Source must be the selected Git repository root")
    if git(root, "rev-parse", "HEAD") != commit:
        raise ValueError("Checkout does not match the requested commit")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("Checkout is dirty; validate a clean immutable snapshot")


def validate_inputs(contract, inputs):
    values, request_id = contract.submission_request({"inputs": inputs})
    if not contract.SHA_RE.fullmatch(values["commit_sha"]):
        raise ValueError("Invalid source commit")
    if values.get("authorization_relationship") not in contract.AUTHORIZATION_RELATIONSHIPS:
        raise ValueError("Missing or invalid authorization relationship")
    if inputs.get("pipeline_commit") != PIPELINE:
        raise ValueError("Request pipeline pin differs from the approved verifier")
    if inputs.get("mode") != "full" or inputs.get("execution_profile") != PROFILE:
        raise ValueError("Request must use full mode and the approved execution profile")
    return request_id


def validate_workflow(workflow):
    if workflow["jobs"]["guard"].get("env", {}).get("PYTHONDONTWRITEBYTECODE") != "1":
        raise ValueError("Guard job must prevent Python bytecode writes to immutable checkouts")
    job = workflow["jobs"]["verify"]
    expected = {
        "repository": "${{ needs.guard.outputs.repository }}",
        "commit": "${{ needs.guard.outputs.commit }}",
        "pipeline_commit": "${{ needs.guard.outputs.pipeline }}",
        "request_id": "${{ needs.guard.outputs.request_id }}",
        "options": "${{ needs.guard.outputs.options }}",
        "mode": "full",
        "execution_profile": PROFILE,
    }
    if job.get("needs") != "guard":
        raise ValueError("Full replay must depend on guard success")
    expected_uses = "PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@" + PIPELINE
    if job.get("uses") != expected_uses or job.get("with") != expected:
        raise ValueError("Workflow and validated input/pipeline bindings differ")


def validate_selection(source, metadata, comparator):
    config = json.loads((source / comparator).read_text())
    selected = [row["lean"] for row in metadata["alignment"]["statements"]]
    if set(config["theorem_names"]) != set(selected) or len(config["theorem_names"]) != len(selected):
        raise ValueError("Metadata and Comparator theorem selections differ")
    if set(config["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
        raise ValueError("Comparator must permit exactly the approved standard axioms")
    for field in ("challenge_module", "solution_module"):
        path = source / (config[field].replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError("Selected source module is missing: " + config[field])


def manifest_guard(source, renderer):
    import urllib.request
    toolchain = (source / "lean-toolchain").read_text().strip()
    verso = renderer.toolchain_verso_commit(toolchain)
    url = f"https://raw.githubusercontent.com/{renderer.VERSO_REPOSITORY}/{verso}/lake-manifest.json"
    with urllib.request.urlopen(url, timeout=60) as response:
        raw = response.read(1024 * 1024 + 1)
    if len(raw) > 1024 * 1024:
        raise ValueError("Verso manifest exceeds the guard limit")
    submitted = (source / "lake-manifest.json").read_bytes()
    merged = renderer.merge_renderer_manifest(json.loads(submitted), json.loads(raw), verso)
    return {"source_manifest_sha256": hashlib.sha256(submitted).hexdigest(),
            "verso_manifest_sha256": hashlib.sha256(raw).hexdigest(),
            "renderer_commit": PIPELINE, "verso_commit": verso,
            "merged_packages": len(merged["packages"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pipeline", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--request-id", required=True)
    parser.add_argument("--entry", required=True, choices=[f"P{i:02}" for i in range(1, 11)])
    parser.add_argument("--authorization-relationship", required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    source, pipeline = args.source.resolve(), args.pipeline.resolve()
    receipt_path = args.receipt.resolve()
    if receipt_path.is_relative_to(source) or receipt_path.is_relative_to(pipeline):
        raise ValueError("Receipt must be outside both immutable checkouts")
    require_snapshot(source, args.commit)
    require_snapshot(pipeline, PIPELINE)
    sys.path.insert(0, str(pipeline))
    contract = importlib.import_module("scripts.submission_contract")
    catalog = json.loads((source / "entries/catalog.json").read_text())
    entry = catalog[args.entry]
    comparator = entry["comparator_config_path"]
    metadata_path = entry["formalization_metadata_path"]
    options = json.dumps({"comparator_config_path": comparator,
                          "formalization_metadata_path": metadata_path,
                          "authorization_relationship": args.authorization_relationship})
    inputs = dict(repository=args.repository, commit=args.commit,
                  pipeline_commit=PIPELINE, request_id=args.request_id,
                  mode="full", execution_profile=PROFILE, options=options)
    validate_inputs(contract, inputs)
    metadata = contract.load_formalization_metadata(source / metadata_path)
    validate_selection(source, metadata, comparator)
    import yaml
    validate_workflow(yaml.safe_load((source / WORKFLOW).read_text()))
    renderer = importlib.import_module("scripts.render_challenge")
    manifest = manifest_guard(source, renderer)
    receipt = {
        "status": "pass",
        "scope": "pinned request/metadata and immutable binding guard; no proof verification",
        "inputs": inputs,
        "entry": args.entry,
        "manifest_guard": manifest,
        "metadata_sha256": hashlib.sha256((source / metadata_path).read_bytes()).hexdigest(),
        "workflow_sha256": hashlib.sha256((source / WORKFLOW).read_bytes()).hexdigest(),
        "comparator_sha256": hashlib.sha256((source / comparator).read_bytes()).hexdigest(),
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as out:
            for key, value in [("repository", args.repository), ("commit", args.commit),
                               ("pipeline", PIPELINE), ("request_id", args.request_id),
                               ("options", options)]:
                out.write(f"{key}={value}\n")
    print("PASS: pinned parser, strict metadata, clean snapshots and replay bindings")


if __name__ == "__main__":
    main()
