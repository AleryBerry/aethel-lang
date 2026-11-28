#!/usr/bin/env python3
"""Exercise the reference source checker with complete Aethel files."""

import argparse
from copy import deepcopy
import json
from pathlib import Path
import re
import subprocess
import tempfile


def invoke(checker: Path, *args: str, timeout: int = 10):
    return subprocess.run(
        [str(checker), *args],
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def model_args(source: Path) -> list[str]:
    model = source.with_suffix(".model.json")
    return ["--model", str(model)] if model.is_file() else []


def check_mir(checker: Path, root: Path, expected: dict) -> None:
    with tempfile.TemporaryDirectory(prefix="aethel-source-mir-") as directory:
        candidate = Path(directory) / "candidate.mir"
        for name, verdict in sorted(expected.items()):
            if not isinstance(verdict, int):
                continue
            source = root / name
            emitted = invoke(checker, "--emit-source-mir", str(source))
            if emitted.returncode != 0 or emitted.stderr:
                raise SystemExit(f"{name}: reference MIR emission failed\n{emitted.stderr}")
            candidate.write_text(emitted.stdout)
            matched = invoke(checker, "--source-mir", str(source), str(candidate), *model_args(source))
            if matched.returncode != 0 or matched.stderr or (
                matched.stdout != f"Source verified (u8 result: {verdict})\n"
            ):
                raise SystemExit(f"{name}: emitted MIR failed to verify\n{matched.stderr}")

        source = root / "branch_taken_then_join.aethel"
        encoded = invoke(checker, "--emit-source-mir", str(source)).stdout
        original = json.loads(encoded)
        changes = {
            "empty body": {"body": "done"},
            "stale version": {"version": 5},
            "different result": {"result": 0},
            "different initializer": {"fields": [["left", 18], ["right", 23]]},
        }
        tampered = [(name, dict(original, **change)) for name, change in changes.items()]
        altered_arm = deepcopy(original)
        altered_arm["body"]["branch"]["no"]["assign"]["value"] = 53
        tampered.append(("changed non-taken arm", altered_arm))

        dynamic_guard = root / "branch_dynamic_equality_selects_fallback.aethel"
        altered_operand = json.loads(invoke(checker, "--emit-source-mir", str(dynamic_guard)).stdout)
        right = altered_operand["body"]["branch"]["right"]["place"]["target"]["field"]
        right["offset"] = 2
        call_source = root / "call_under_disjoint_view.aethel"
        call_ir = json.loads(invoke(checker, "--emit-source-mir", str(call_source)).stdout)
        altered_contract = deepcopy(call_ir)
        altered_contract["functions"][0]["paths"] = ["left"]
        altered_helper = deepcopy(call_ir)
        altered_helper["functions"][0]["body"] = "done"
        loop_source = root / "loop_snapshots_bound_before_body_writes.aethel"
        altered_bound = json.loads(invoke(checker, "--emit-source-mir", str(loop_source)).stdout)
        altered_bound["body"]["range"]["stop"] = {"place": {"target": {"field": {"offset": 1}}}}
        endpoints_source = root / "range_dynamic_endpoints_snapshot_before_both_stores.aethel"
        altered_endpoints = json.loads(invoke(checker, "--emit-source-mir", str(endpoints_source)).stdout)
        loop = altered_endpoints["body"]["range"]
        loop["first"], loop["stop"] = loop["stop"], loop["first"]
        copy_source = root / "copy_reads_rhs_before_overwriting.aethel"
        altered_copy = json.loads(invoke(checker, "--emit-source-mir", str(copy_source)).stdout)
        altered_copy["body"]["copy"]["source"] = {"field": {"offset": 1}}
        return_source = root / "value_call_reads_callee_updated_field.aethel"
        altered_return = json.loads(invoke(checker, "--emit-source-mir", str(return_source)).stdout)
        altered_return["functions"][0]["result"] = {"byte": {"offset": 1}}
        view_source = root / "returned_shared_view_restores_field_after_branch.aethel"
        altered_view = json.loads(invoke(checker, "--emit-source-mir", str(view_source)).stdout)
        altered_view["functions"][0]["result"]["view"]["mode"] = "exclusive"
        while_source = root / "while_countdown_runs_from_maximum_byte.aethel"
        countdown_ir = json.loads(invoke(checker, "--emit-source-mir", str(while_source)).stdout)
        altered_countdown = deepcopy(countdown_ir)
        altered_countdown["body"]["repeatFrom"]["body"]["sequence"]["body"]["subtractFrom"]["amount"] = 0
        altered_stride = deepcopy(countdown_ir)
        altered_stride["body"]["repeatFrom"]["iterations"]["countdown"]["amount"] = 2
        threshold_source = root / "while_threshold_stops_at_nonzero_bound.aethel"
        altered_threshold = json.loads(invoke(checker, "--emit-source-mir", str(threshold_source)).stdout)
        altered_threshold["body"]["repeatFrom"]["iterations"]["countdown"]["threshold"] = 6
        fork_source = root / "fork_disjoint_stores_keep_task_order.aethel"
        altered_store = json.loads(invoke(checker, "--emit-source-mir", str(fork_source)).stdout)
        altered_store["body"]["fork"]["tasks"][1][0]["write"]["place"] = 0
        fork_read_source = root / "fork_shares_read_only_input_between_writers.aethel"
        altered_fork_read = json.loads(invoke(checker, "--emit-source-mir", str(fork_read_source)).stdout)
        altered_fork_read["body"]["fork"]["tasks"][1][0]["read"]["place"] = 1
        scope_source = root / "last_use_ends_shared_view_before_same_block_store.aethel"
        altered_scope = json.loads(invoke(checker, "--emit-source-mir", str(scope_source)).stdout)
        scope = altered_scope["body"]["withView"]
        scope["body"]["discard"]["next"] = scope["next"]["sequence"]["body"]
        scope["next"] = scope["next"]["sequence"]["next"]
        parent_source = root / "last_use_preserves_parent_slot_in_suffix.aethel"
        altered_slot = json.loads(invoke(checker, "--emit-source-mir", str(parent_source)).stdout)
        parent_scope = altered_slot["body"]["withView"]["body"]["withView"]
        parent_copy = parent_scope["next"]["sequence"]["body"]["assign"]["next"]["copy"]
        altered_origin = deepcopy(altered_slot)
        origin_scope = altered_origin["body"]["withView"]["body"]["withView"]
        origin_copy = origin_scope["next"]["sequence"]["body"]["assign"]["next"]["copy"]
        origin_copy["source"]["view"]["offset"] = 0
        parent_copy["source"]["view"]["index"] = 1
        view_store_source = root / "view_store_literal_updates_origin.aethel"
        altered_view_store = json.loads(invoke(checker, "--emit-source-mir", str(view_store_source)).stdout)
        view_store = altered_view_store["body"]["withView"]["body"]["assign"]
        view_store["target"]["view"]["offset"] = 1
        move_source = root / "move_chain_preserves_record_bytes.aethel"
        altered_move = json.loads(invoke(checker, "--emit-source-mir", str(move_source)).stdout)
        altered_move["moves"][1]["fromName"] = "seed"
        cold_source = root / "production_mir_distinguishes_cold_setting.aethel"
        hot_source = root / "production_mir_distinguishes_hot_setting.aethel"
        hot_mir = json.loads(invoke(checker, "--emit-source-mir", str(hot_source)).stdout)
        capture_source = root / "closure_captures_before_shadowing.aethel"
        altered_capture = json.loads(invoke(checker, "--emit-source-mir", str(capture_source)).stdout)
        captured_body = altered_capture["expression"]["letBind"]["body"]["letBind"]["val"]["lam"]["body"]
        captured_body["var"]["id"] = 1
        tuple_source = root / "pure_tuple_nested_capture.aethel"
        altered_projection = json.loads(invoke(checker, "--emit-source-mir", str(tuple_source)).stdout)
        tuple_closure = altered_projection["expression"]["letBind"]["body"]["letBind"]["val"]["lam"]["body"]
        selected = tuple_closure["matchTag"]["onMatch"]
        tuple_closure["matchTag"]["onMatch"] = {"snd": selected["fst"]}
        named_source = root / "pure_named_helper_keeps_earlier_binding.aethel"
        altered_definition = json.loads(invoke(checker, "--emit-source-mir", str(named_source)).stdout)
        named_body = altered_definition["expression"]["letBind"]["val"]["lam"]["body"]
        named_body["matchTag"]["onMatch"]["int"]["val"] = 50
        argument_source = root / "pure_multi_arguments_keep_parameter_order.aethel"
        altered_arguments = json.loads(invoke(checker, "--emit-source-mir", str(argument_source)).stdout)
        arguments = altered_arguments["expression"]["letBind"]["body"]["app"]["arg"]["pair"]["snd"]["pair"]
        arguments["fst"], arguments["snd"] = arguments["snd"], arguments["fst"]
        result_source = root / "result_match_reads_selected_payload.aethel"
        result_mir = json.loads(invoke(checker, "--emit-source-mir", str(result_source)).stdout)
        altered_result_tag = deepcopy(result_mir)
        altered_result_tag["expression"]["matchSum"]["scrutinee"]["inject"]["left"] = False
        altered_result_arm = deepcopy(result_mir)
        altered_result_arm["expression"]["matchSum"]["onRight"]["int"]["val"] = 9
        collection_source = root / "collection_guarded_unequal_rows_borrow_exclusively.aethel"
        collection_mir = json.loads(invoke(checker, "--emit-source-mir", str(collection_source)).stdout)
        altered_collection_layout = dict(collection_mir, layout="soa")
        altered_collection_cell = deepcopy(collection_mir)
        altered_collection_cell["initial"][1][0] = 119
        altered_collection_result = deepcopy(collection_mir)
        altered_collection_result["result"]["cell"]["field"] = "right"
        reborrow_source = root / "reborrow_outer_index_with_inner_sibling.aethel"
        altered_reborrow = json.loads(invoke(checker, "--emit-source-mir", str(reborrow_source)).stdout)
        reborrow = altered_reborrow["body"]["withView"]["body"]["withView"]["body"]["reborrow"]
        reborrow["parent"] = 0
        rust_source = root / "rust_call_updates_moved_owner_in_call_order.aethel"
        rust_mir = json.loads(invoke(checker, "--emit-source-mir", str(rust_source)).stdout)
        altered_rust_symbol = deepcopy(rust_mir)
        altered_rust_symbol["calls"][0]["target"]["symbol"] = "last"
        altered_rust_mode = deepcopy(rust_mir)
        altered_rust_mode["calls"][0]["fields"][0][1] = "shared"
        altered_rust_order = dict(rust_mir, calls=list(reversed(rust_mir["calls"])))
        changed_sources = [
            (source, name, ir) for name, ir in tampered
        ] + [
            (dynamic_guard, "different right field in branch guard", altered_operand),
            (call_source, "changed contract", altered_contract),
            (call_source, "missing helper body", altered_helper),
            (loop_source, "different runtime loop bound", altered_bound),
            (endpoints_source, "swapped range endpoints", altered_endpoints),
            (copy_source, "different copy operand", altered_copy),
            (return_source, "different callee return field", altered_return),
            (view_source, "different returned view permission", altered_view),
            (while_source, "non-decreasing while body", altered_countdown),
            (while_source, "countdown schedule with a different stride", altered_stride),
            (threshold_source, "countdown schedule with a different threshold", altered_threshold),
            (fork_source, "changed fork store destination", altered_store),
            (fork_read_source, "changed fork read to a sibling's written field", altered_fork_read),
            (scope_source, "store moved before last-use release", altered_scope),
            (parent_source, "stale view slot after last-use release", altered_slot),
            (parent_source, "view load claims a sibling byte", altered_origin),
            (view_store_source, "view store claims a sibling byte", altered_view_store),
            (move_source, "move from a retired name", altered_move),
            (cold_source, "different thermostat store value", hot_mir),
            (capture_source, "changed closure capture", altered_capture),
            (tuple_source, "changed tuple projection", altered_projection),
            (named_source, "changed named helper result", altered_definition),
            (argument_source, "swapped same-typed arguments", altered_arguments),
            (result_source, "changed Result constructor with the same payload type", altered_result_tag),
            (result_source, "changed non-selected Result arm", altered_result_arm),
            (collection_source, "different collection layout from the declared override", altered_collection_layout),
            (collection_source, "changed overwritten collection initializer", altered_collection_cell),
            (collection_source, "different field in the final indexed read", altered_collection_result),
            (reborrow_source, "changed reborrow parent", altered_reborrow),
            (rust_source, "different linked Rust symbol", altered_rust_symbol),
            (rust_source, "different borrowed argument mode", altered_rust_mode),
            (rust_source, "changed Rust call order", altered_rust_order),
        ]
        for actual_source, name, ir in changed_sources:
            candidate.write_text(json.dumps(ir, separators=(",", ":"), sort_keys=True))
            rejected = invoke(checker, "--source-mir", str(actual_source), str(candidate))
            if rejected.returncode != 1 or not rejected.stderr.rstrip().endswith(".sourceMIRMismatch"):
                raise SystemExit(f"{name}: candidate should fail correspondence\n{rejected.stderr}")

        for text in ["mir_version 1\nfn main\nend_fn\n", encoded.strip()[:-1] + ',"extra":0}']:
            candidate.write_text(text)
            rejected = invoke(checker, "--source-mir", str(source), str(candidate))
            if rejected.returncode != 1 or not rejected.stderr.rstrip().endswith(".invalidSourceMIR"):
                raise SystemExit(f"unsupported MIR encoding should fail\n{rejected.stderr}")

    print("Source MIR emission, matching, and tamper checks passed")


def check_rust_models(checker: Path, sources: Path) -> None:
    source = sources / "rust_call_updates_moved_owner_in_call_order.aethel"
    original = json.loads(source.with_suffix(".model.json").read_text())
    unlinked = deepcopy(original)
    unlinked[1]["target"]["package"] = "another_batch"
    past_end = deepcopy(original)
    past_end[1]["accesses"][0]["address"]["byte"] = 1
    duplicate = original + [original[0]]
    with tempfile.TemporaryDirectory(prefix="aethel-rust-model-") as directory:
        candidate = Path(directory) / "adapter.json"
        for name, model, diagnostic in [
            ("wrong crate", unlinked, "rustTraceRejected"),
            ("byte just outside the slice", past_end, "rustTraceRejected"),
            ("duplicate symbol", duplicate, "invalidRustModel"),
            ("missing model", None, "rustModelRequired"),
        ]:
            options = []
            if model is not None:
                candidate.write_text(json.dumps(model))
                options = ["--model", str(candidate)]
            failed = invoke(checker, "--source", str(source), *options)
            if failed.returncode != 1 or failed.stdout or f".Error.{diagnostic}" not in failed.stderr:
                raise SystemExit(f"{name}: expected {diagnostic}\n{failed.stdout}{failed.stderr}")
    print("Rust model symbol binding, slice bounds, and model admission checks passed")


def check_laws(checker: Path, sources: Path) -> None:
    laws = sources.parent / "source-laws"
    cap_source = sources / "law_cap_applies_to_current_source.aethel"
    limit_source = sources / "law_limit_uses_current_pair_fields.aethel"
    triple = sources / "value_call_transitive_return.aethel"
    pure = sources / "law_pure_checks_both_sum_variants.aethel"
    changed_pure = sources / "law_pure_detects_changed_predicate.aethel"
    cap_proof = "Law capped_output proved for all 65536 initialized inputs\n"
    successes = [
        (cap_source, "cap.aethel", cap_proof),
        (cap_source, "input_field_bound.aethel", "Law never_increases proved for all 65536 initialized inputs\n"),
        (limit_source, "input_field_limit.aethel", "Law respects_limit proved for all 65536 initialized inputs\n"),
        (triple, "byte_type_bound.aethel", "Law result_in_byte_range proved for all 16777216 initialized inputs\n"),
        (triple, "guarded_budget.aethel", "Law stage_under_guard proved for all 16777216 initialized inputs\n"),
        (triple, "guarded_impossible.aethel", "Law impossible_input proved vacuously (no initialized input satisfies the guard)\n"),
        (pure, "pure_proved.aethel",
         "Law both_variants proved for all 258 typed inputs\n"
         "Law exclusive_flags proved for all 4 typed inputs\n"
         "Law exact_budget proved for all 65536 typed inputs\n"),
        (pure, "pure_linked_predicate.aethel", "Law handles_every_request proved for all 258 typed inputs\n"),
    ]
    for source, name, expected in successes:
        proved = invoke(checker, "--source-law", str(source), str(laws / name))
        if proved.returncode != 0 or proved.stderr or proved.stdout != expected:
            raise SystemExit(f"{name}: expected proof\n{proved.stdout}{proved.stderr}")

    failures = [
        (cap_source, "counterexample.aethel", "Law no_seven is false on [7, 0] with result 7"),
        (cap_source, "unknown_helper.aethel", ".unknownHelper \"absent\""),
        (triple, "budget.aethel", ".budgetExceeded 16777216"),
        (triple, "byte_type_counterexample.aethel", "Law never_in_byte_range is false on [0, 0, 0] with result 83"),
        (cap_source, "guarded_counterexample.aethel", "Law bounded_under_guard is false on [8, 0] with result 8"),
        (cap_source, "input_field_changed_counterexample.aethel",
         "Law original_value_preserved is false on [101, 0] with result 100"),
        (limit_source, "input_field_limit_counterexample.aethel",
         "Law preserves_large_request is false on [201, 0] with result 0"),
        (cap_source, "input_field_unknown.aethel", '.unknownField "row" "absent")'),
        (triple, "guarded_type_counterexample.aethel", "Law never_byte_under_guard is false on [0, 10, 0] with result 83"),
        (triple, "guarded_unknown_field.aethel", '.unknownField "triple" "missing")'),
    ]
    failures += [
        (changed_pure, "pure_linked_predicate.aethel",
         "Law handles_every_request is false on Err(true) with result false"),
        (pure, "pure_budget.aethel", ".budgetExceeded 16777216"),
        (pure, "pure_wrong_argument.aethel", '.syntax "( value ) }"'),
    ]
    for source, name, diagnostic in failures:
        rejected = invoke(checker, "--source-law", str(source), str(laws / name))
        if rejected.returncode != 1 or rejected.stdout or not rejected.stderr.rstrip().endswith(diagnostic):
            raise SystemExit(f"{name}: expected {diagnostic!r}\n{rejected.stdout}{rejected.stderr}")

    mixed = invoke(checker, "--source-law", str(cap_source), str(laws / "mixed.aethel"))
    if (
        mixed.returncode != 1
        or mixed.stdout != cap_proof
        or mixed.stderr.splitlines() != [
            "Law no_seven is false on [7, 0] with result 7",
            'Law unrelated_output verification failed: Aethel.SourceVerification.ReturnLawError.unknownHelper "absent"',
        ]
    ):
        raise SystemExit(f"Mixed law file should report all declarations\n{mixed.stdout}{mixed.stderr}")

    mixed_pure = invoke(checker, "--source-law", str(pure), str(laws / "pure_mixed.aethel"))
    if (
        mixed_pure.returncode != 1
        or mixed_pure.stdout != "Law accepted_cases proved for all 258 typed inputs\n"
        or mixed_pure.stderr.splitlines() != [
            "Law no_blocked_request is false on Err(true) with result false",
            "Law unexpected_type verification failed: Aethel.SourceVerification.PureLawError.source"
            " (Aethel.SourceVerification.Error.coreType)",
            "Law unknown_predicate verification failed: Aethel.SourceVerification.PureLawError.source"
            ' (Aethel.SourceVerification.Error.unknownBinding "absent")',
        ]
    ):
        raise SystemExit(f"Mixed pure law file should report all declarations\n{mixed_pure.stdout}{mixed_pure.stderr}")

    unsupported = invoke(checker, "--source-law", str(pure), str(laws / "pure_unsupported_domain.aethel"))
    if unsupported.returncode != 1 or unsupported.stdout or "PureLawError.unsupportedDomain" not in unsupported.stderr:
        raise SystemExit(f"Expected unsupported function domain\n{unsupported.stdout}{unsupported.stderr}")

    print("Source record and typed predicate law proof, counterexample, resolution, and budget checks passed")


def check_invariant_packages(checker: Path, fixtures: Path) -> None:
    from tempfile import TemporaryDirectory

    fixture = fixtures / "replace_client.aethel"
    selector = "Laws.CharacterLaws.x_and_y_same"
    for name, status, message in [
        (fixture.name, 0, f"Invariant {selector} proved"),
        ("invalid_client.aethel", 1, f"FALSIFIED {selector}"),
        ("repair_client.aethel", 1, f"FALSIFIED {selector}"),
        ("zero_client.aethel", 0, f"Invariant {selector} proved"),
        ("view_client.aethel", 1, f"FALSIFIED {selector}"),
    ]:
        result = invoke(checker, "--law-package", str(fixtures / name))
        if result.returncode != status or message not in result.stdout + result.stderr:
            raise SystemExit(f"{name}: {result.stdout}{result.stderr}")

    with TemporaryDirectory() as temporary:
        root = Path(temporary)
        namespace = root / "Laws"
        namespace.mkdir()
        definitions = (fixtures / "Laws" / "CharacterLaws.aethel").read_text()
        law_file = namespace / "CharacterLaws.aethel"
        owner = root / "Character.aethel"
        entry = root / fixture.name
        entry.write_text(fixture.read_text())
        for imports, extra, status, message in [
            ("use law Laws.CharacterLaws", "", 0, "proved for every observed state"),
            (f"use law Laws.CharacterLaws\nuse law {selector}", "", 0, "proved for every observed state"),
            ("use law Laws.CharacterLaws.typo", "", 1, "unknown law"),
            (f"use law {selector}", definitions.split("\n", 1)[1], 1, "duplicate declaration"),
        ]:
            owner.write_text(imports + "\ntype Character { x: u8, y: u8 }\n")
            law_file.write_text(definitions + extra)
            result = invoke(checker, "--law-package", str(entry))
            if result.returncode != status or message not in result.stdout + result.stderr:
                raise SystemExit(f"{imports}: {result.stdout}{result.stderr}")
            if status == 0 and result.stdout.count(selector) != 1:
                raise SystemExit("Overlapping selections must check the invariant once")

        owner.write_text("""type Character {
  x: u8,
  y: u8,
  law x_and_y_same(c: Character) { always c.x == c.y }
}
""")
        for filename, status, message in [
            (fixture.name, 0, "Character.x_and_y_same proved"),
            ("repair_client.aethel", 1, "FALSIFIED Character.x_and_y_same"),
        ]:
            entry.write_text((fixtures / filename).read_text())
            result = invoke(checker, "--law-package", str(entry))
            if result.returncode != status or message not in result.stdout + result.stderr:
                raise SystemExit(f"Inline type law in {filename}: {result.stdout}{result.stderr}")
        owner.write_text("use law " + selector + "\ntype Character { x: u8, y: u8 }\n")
        law_file.write_text(definitions.replace("law x_and_y_same", "invariant x_and_y_same"))
        result = invoke(checker, "--law-package", str(entry))
        if result.returncode != 1 or "unsupported declaration" not in result.stderr:
            raise SystemExit(f"Legacy invariant declaration: {result.stdout}{result.stderr}")


def compare_production_mir(checker: Path, compiler: Path, sources: Path) -> bool:
    certificates = []
    with tempfile.TemporaryDirectory(prefix="aethel-production-mir-") as directory:
        for setting in ("cold", "hot"):
            source = sources / f"production_mir_distinguishes_{setting}_setting.aethel"
            emitted = invoke(compiler, "emit-mir", str(source))
            if emitted.returncode != 0 or emitted.stderr:
                raise SystemExit(f"{source.name}: production MIR emission failed\n{emitted.stderr}")
            certificate = Path(directory) / f"{setting}.mir"
            certificate.write_text(emitted.stdout)
            validated = invoke(checker, str(certificate))
            if validated.returncode != 0 or validated.stderr:
                raise SystemExit(f"{source.name}: production MIR validation failed\n{validated.stderr}")
            certificates.append(emitted.stdout)

    if certificates[0] == certificates[1]:
        print("Production MIR collision: identical valid certificates for stores returning 34 and 79")
        return False
    print("Production MIR distinguished the two thermostat stores")
    return True


def compare_native(checker: Path, compiler: Path, sources: Path, expected: dict) -> None:
    compiler = compiler.resolve()
    matched_results = 0
    matched_rejections = 0
    results = sum(isinstance(verdict, int) for verdict in expected.values())
    with tempfile.TemporaryDirectory(prefix="aethel-native-source-") as directory:
        for name, verdict in sorted(expected.items()):
            accepts = isinstance(verdict, int)
            process = subprocess.run(
                [str(compiler), "run" if accepts else "check", str(sources / name)],
                cwd=directory,
                capture_output=True,
                text=True,
                timeout=45,
            )
            if accepts:
                if process.returncode == verdict and not process.stderr:
                    matched_results += 1
                else:
                    print(f"{name}: expected native result {verdict}, got exit {process.returncode}")
                    print(process.stderr.rstrip())
            elif process.returncode != 0 and process.stderr:
                matched_rejections += 1
            else:
                print(f"{name}: reference rejected with {verdict}, native check exited {process.returncode}")

    rejections = len(expected) - results
    print(f"Native matched {matched_results}/{results} results and {matched_rejections}/{rejections} rejections")
    mir_distinguishes_stores = compare_production_mir(checker, compiler, sources)
    if matched_results != results or matched_rejections != rejections or not mir_distinguishes_stores:
        raise SystemExit(1)


def check_packed_sources(checker: Path, test_root: Path) -> None:
    sources = test_root / "packed-source"
    accepted = {
        "reordered_wide_signed": ("i31", -1073741824, 10),
        "maximum_width_shared_boundary": ("u33", 4294967296, 8197),
        "fork_requires_distinct_slots": ("u5", 17, 16),
        "nested_view_updates_unaligned_leaf": ("u8", 9, 5),
        "tag_replacement_preserves_sibling": ("u3", 7, 9),
        "flat_record_keeps_declaration_order": ("u8", 23, 20),
        "nested_flat_record_keeps_compact_parent": ("u32", 4294967295, 20),
        "flat_variant_payload_requires_address": ("u33", 8589934591, 20),
        "nested_variant_product_preserves_component_codes": ("u5", 29, 8),
        "return_aligned_variant_field": ("u32", 2864434397, 20),
        "return_compact_variant_field": ("u35", 34359738367, 8),
    }
    for name, (kind, value, size) in accepted.items():
        result = invoke(
            checker, "--packed-source", str(sources / f"{name}.aethel"),
            timeout=45 if name == "maximum_width_shared_boundary" else 10,
        )
        expected = f"Packed source verified ({kind} result: {value}, bytes: {size})\n"
        if result.returncode or result.stderr or result.stdout != expected:
            raise SystemExit(f"{name}: expected {expected}{result.stdout}{result.stderr}")
    for name in ["fork_rejects_same_field", "shared_view_cannot_write"]:
        result = invoke(checker, "--packed-source", str(sources / f"{name}.aethel"))
        if result.returncode != 1 or "invalid packed operation or physical footprint" not in result.stderr:
            raise SystemExit(f"{name}: expected a packed permission rejection\n{result.stdout}{result.stderr}")
    for name, diagnostic in {
        "return_variant_field_rejects_inactive_constructor": "invalid packed operation or physical footprint",
        "return_variant_field_rejects_out_of_range_index": "variant component index out of range",
    }.items():
        result = invoke(checker, "--packed-source", str(sources / f"{name}.aethel"))
        if result.returncode != 1 or diagnostic not in result.stderr:
            raise SystemExit(f"{name}: expected {diagnostic}\n{result.stdout}{result.stderr}")

    projected_source = sources / "return_compact_variant_field.aethel"
    projected = invoke(checker, "--emit-packed-mir", str(projected_source))
    if projected.returncode or projected.stderr:
        raise SystemExit(f"Projected source MIR emission failed\n{projected.stdout}{projected.stderr}")
    projected_mir = json.loads(projected.stdout)
    with tempfile.TemporaryDirectory(prefix="aethel-packed-projected-return-") as directory:
        mir = Path(directory) / "return.json"
        mir.write_text(projected.stdout)
        matched = invoke(checker, "--packed-source-mir", str(projected_source), str(mir))
        if matched.returncode or matched.stderr:
            raise SystemExit(f"Source and projected return MIR disagree\n{matched.stdout}{matched.stderr}")
        projected_mir["operations"][-3]["loadPayloadField"]["steps"] = ["right", "left", "right", "left"]
        mir.write_text(json.dumps(projected_mir))
        standalone = invoke(checker, "--packed-mir", str(mir))
        if standalone.returncode or standalone.stderr:
            raise SystemExit(f"Alternate valid selector rejected by standalone MIR\n{standalone.stdout}{standalone.stderr}")
        tampered = invoke(checker, "--packed-source-mir", str(projected_source), str(mir))
        if tampered.returncode != 1 or "packed MIR differs from the source operations" not in tampered.stderr:
            raise SystemExit(f"Source accepted a different return selector\n{tampered.stdout}{tampered.stderr}")

    nested_variant = sources / "nested_variant_product_preserves_component_codes.aethel"
    nested_emitted = invoke(checker, "--emit-packed-mir", str(nested_variant))
    if nested_emitted.returncode or nested_emitted.stderr:
        raise SystemExit(f"Nested variant MIR emission failed\n{nested_emitted.stdout}{nested_emitted.stderr}")
    expected_nested_code = 1 + (5 << 1) + (34359738367 << 4) + (8191 << 39)
    nested_mir = json.loads(nested_emitted.stdout)
    if nested_mir["initial"] != [[[0], expected_nested_code], [[1], 29]]:
        raise SystemExit("The nested variant initializer lost a component or used the wrong offset")
    variant_entry, guard_entry = nested_mir["initial"]
    with tempfile.TemporaryDirectory(prefix="aethel-packed-initial-paths-") as directory:
        mir = Path(directory) / "initial.json"
        for name, initial in {
            "missing guard": [variant_entry],
            "duplicate variant": [variant_entry, variant_entry, guard_entry],
            "swapped declaration order": [guard_entry, variant_entry],
        }.items():
            mir.write_text(json.dumps(dict(nested_mir, initial=initial)))
            rejected = invoke(checker, "--packed-mir", str(mir))
            if rejected.returncode != 1 or "initial values must match declaration paths in order" not in rejected.stderr:
                raise SystemExit(f"Packed initializer {name} was accepted\n{rejected.stdout}{rejected.stderr}")

    variant_source = sources / "flat_variant_payload_requires_address.aethel"
    variant_emitted = invoke(checker, "--emit-packed-mir", str(variant_source))
    if variant_emitted.returncode or variant_emitted.stderr:
        raise SystemExit(f"Aligned variant MIR emission failed\n{variant_emitted.stdout}{variant_emitted.stderr}")
    variant_mir = json.loads(variant_emitted.stdout)
    variant_layout = variant_mir["layout"]
    placements = [(f["byteOffset"], f.get("bitOffset"), f["width"]) for f in variant_layout["fields"]]
    initial_code = 1 + (5 << 32) + (305419896 << 64)
    if variant_layout["alignment"] != 4 or placements != [(16, 1, 1), (0, None, 96), (12, 0, 33)]:
        raise SystemExit(f"Unexpected layout for aligned variant payload {placements}")
    if variant_mir["initial"][1] != [[1], initial_code]:
        raise SystemExit("The initializer lost the flat payload's aligned word offset")
    with tempfile.TemporaryDirectory(prefix="aethel-aligned-variant-") as directory:
        mir = Path(directory) / "variant.json"
        mir.write_text(variant_emitted.stdout)
        matched = invoke(checker, "--packed-source-mir", str(variant_source), str(mir))
        if matched.returncode or matched.stderr:
            raise SystemExit(f"Source and aligned variant MIR disagree\n{matched.stdout}{matched.stderr}")
        variant_mir["initial"][1][1] = initial_code + (1 << 8)
        mir.write_text(json.dumps(variant_mir))
        rejected = invoke(checker, "--packed-mir", str(mir))
        if rejected.returncode != 1 or "invalid packed initializer" not in rejected.stderr:
            raise SystemExit(f"Nonzero variant padding was accepted\n{rejected.stdout}{rejected.stderr}")

    flat_layouts = {
        "flat_record_keeps_declaration_order": [
            ([0], 0, None), ([1, 0], 4, None), ([1, 1], 8, None), ([1, 2], 12, None), ([2], 16, None),
        ],
        "nested_flat_record_keeps_compact_parent": [
            ([0], 16, 1), ([1, 0], 0, None), ([1, 1], 4, None), ([1, 2], 8, None), ([2], 12, 0),
        ],
    }
    for name, expected in flat_layouts.items():
        flat_source = sources / f"{name}.aethel"
        flat_emitted = invoke(checker, "--emit-packed-mir", str(flat_source))
        if flat_emitted.returncode or flat_emitted.stderr:
            raise SystemExit(f"{name}: flat MIR emission failed\n{flat_emitted.stdout}{flat_emitted.stderr}")
        flat_mir = json.loads(flat_emitted.stdout)
        fields = flat_mir["layout"]["fields"]
        placements = [(field["path"], field["byteOffset"], field.get("bitOffset")) for field in fields]
        if flat_mir["layout"]["alignment"] != 4 or placements != expected:
            raise SystemExit(f"{name}: unexpected declaration-order placement {placements}")
        with tempfile.TemporaryDirectory(prefix="aethel-flat-mir-") as directory:
            mir = Path(directory) / "flat.json"
            mir.write_text(flat_emitted.stdout)
            matched = invoke(checker, "--packed-source-mir", str(flat_source), str(mir))
            if matched.returncode:
                raise SystemExit(f"{name}: flat source did not verify with its MIR\n{matched.stdout}{matched.stderr}")
            fields[1]["byteOffset"], fields[3]["byteOffset"] = fields[3]["byteOffset"], fields[1]["byteOffset"]
            mir.write_text(json.dumps(flat_mir))
            rejected = invoke(checker, "--packed-mir", str(mir))
            if rejected.returncode != 1 or "packed layout does not match" not in rejected.stderr:
                raise SystemExit(f"{name}: reordered flat fields were accepted\n{rejected.stdout}{rejected.stderr}")

    source = sources / "reordered_wide_signed.aethel"
    emitted = invoke(checker, "--emit-packed-mir", str(source))
    if emitted.returncode or emitted.stderr:
        raise SystemExit(f"Packed MIR emission failed\n{emitted.stdout}{emitted.stderr}")
    tagged_source = sources / "tag_replacement_preserves_sibling.aethel"
    tagged = invoke(checker, "--emit-packed-mir", str(tagged_source))
    if tagged.returncode or tagged.stderr:
        raise SystemExit(f"Packed float encoding failed\n{tagged.stdout}{tagged.stderr}")
    float_codes = {tuple(path): value for path, value in json.loads(tagged.stdout)["initial"]}
    if float_codes.get((1,)) != 1 + 4 * 0x80000000:
        raise SystemExit("Packed MIR did not preserve the sign bit of the float initializer")
    with tempfile.TemporaryDirectory(prefix="aethel-packed-mir-") as directory:
        mir = Path(directory) / "sample.json"
        mir.write_text(emitted.stdout)
        verified = invoke(checker, "--packed-mir", str(mir))
        matched = invoke(checker, "--packed-source-mir", str(source), str(mir))
        if verified.returncode or matched.returncode:
            raise SystemExit(f"Packed MIR verification failed\n{verified.stderr}{matched.stderr}")
        different = Path(directory) / "different.aethel"
        different.write_text(source.read_text().replace("-1073741824", "-15"))
        rejected = invoke(checker, "--packed-source-mir", str(different), str(mir))
        if rejected.returncode != 1 or "differs from the source operations" not in rejected.stderr:
            raise SystemExit(f"Packed source accepted another program's MIR\n{rejected.stdout}{rejected.stderr}")
        split_decimal = Path(directory) / "split_decimal.aethel"
        split_decimal.write_text(tagged_source.read_text().replace("-0.0", "-0 . 0"))
        rejected = invoke(checker, "--packed-source", str(split_decimal))
        if rejected.returncode != 1 or "decimal f32 literal" not in rejected.stderr:
            raise SystemExit(f"Packed source accepted a split decimal token\n{rejected.stdout}{rejected.stderr}")
    print("Packed source fixtures, source-bound MIR, and native-independent execution passed")


def main(checker: Path, native: Path | None = None) -> None:
    checker = checker.resolve()
    root = Path(__file__).resolve().parents[1] / "tests" / "source-verification"
    expected = json.loads((root / "expected.json").read_text())
    actual_files = {path.name for path in root.glob("*.aethel")}
    if actual_files != set(expected):
        raise SystemExit(f"Source fixtures and expectations differ: {actual_files ^ set(expected)}")

    accepted = 0
    for name, verdict in sorted(expected.items()):
        source = root / name
        result = invoke(checker, "--source", str(source), *model_args(source))
        if isinstance(verdict, int):
            success = result.returncode == 0 and not result.stderr and (
                result.stdout == f"Source verified (u8 result: {verdict})\n"
            )
            accepted += 1
        else:
            success = result.returncode == 1 and not result.stdout and re.match(
                rf"Source verification failed: Aethel\.SourceVerification\.Error\.{verdict}\b",
                result.stderr,
            )
        if not success:
            raise SystemExit(
                f"{name}: expected {verdict!r}, got exit {result.returncode}\n"
                f"{result.stdout}{result.stderr}"
            )
    print(f"Source verification fixtures passed ({accepted} accepted, {len(expected) - accepted} rejected)")
    check_mir(checker, root, expected)
    check_rust_models(checker, root)
    check_laws(checker, root)
    check_invariant_packages(checker, root.parent / "invariants")
    check_packed_sources(checker, root.parent)
    if native is not None:
        compare_native(checker, native, root, expected)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checker", type=Path)
    parser.add_argument("--native", type=Path, help="compare the reference verdicts with an Aethel compiler")
    args = parser.parse_args()
    main(args.checker, args.native)
