// Exact view/Rust mutation anchors migrated from retained paired experiments.
// No Latte runtime is needed to execute these checks.
export const deleteControlFixtures = [
  {
    "name": "delete-permutation-sift-loses-swap-value",
    "component": "permutation",
    "original": "sift-loses-swap-value",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.sift_preserves_births",
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn sift_births(",
      "before": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= finish / 2 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child + 1]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = old;\n        root = child;\n    }\n    values\n}",
      "after": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= finish / 2 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child + 1]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = values[root];\n        root = child;\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-drain-loses-swap-value",
    "component": "permutation",
    "original": "drain-loses-swap-value",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.drain_preserves_births",
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn drain_births(",
      "before": "fn drain_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..len {\n        let finish = len - 1 - step;\n        if values.is_empty() || finish >= values.len() { break; }\n        let old = values[0];\n        values[0] = values[finish];\n        values[finish] = old;\n        values = sift_births(values, 0, finish);\n    }\n    values\n}",
      "after": "fn drain_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..len {\n        let finish = len - 1 - step;\n        if values.is_empty() || finish >= values.len() { break; }\n        let old = values[0];\n        values[0] = values[finish];\n        values[finish] = values[0];\n        values = sift_births(values, 0, finish);\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-heap-wrong-input-argument",
    "component": "permutation",
    "original": "heap-wrong-input-argument",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.heap_preserves_births",
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn heap_births(",
      "before": "fn heap_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..(len / 2) {\n        if step < len / 2 {\n            values = sift_births(values, len / 2 - 1 - step, len);\n        }\n    }\n    values\n}",
      "after": "fn heap_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..(len / 2) {\n        if step < len / 2 {\n            values = sift_births(Vec::new(), len / 2 - 1 - step, len);\n        }\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-drain-wrong-input-argument",
    "component": "permutation",
    "original": "drain-wrong-input-argument",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.drain_preserves_births",
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn drain_births(",
      "before": "fn drain_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..len {\n        let finish = len - 1 - step;\n        if values.is_empty() || finish >= values.len() { break; }\n        let old = values[0];\n        values[0] = values[finish];\n        values[finish] = old;\n        values = sift_births(values, 0, finish);\n    }\n    values\n}",
      "after": "fn drain_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..len {\n        let finish = len - 1 - step;\n        if values.is_empty() || finish >= values.len() { break; }\n        let old = values[0];\n        values[0] = values[finish];\n        values[finish] = old;\n        values = sift_births(Vec::new(), 0, finish);\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-without-sift-contract",
    "component": "permutation",
    "original": "without-sift-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.heap_preserves_births",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "sift_preserves_births",
      "before": "let sift_preserves_births (values: births) (start: usize) (finish: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) [SMTPat (Native.sift_births values start finish)] =\n  break_preserve_any (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (sift_items (Alloc.Vec.impl_1__as_slice values));\n  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let sift_preserves_births (values: births) (start: usize) (finish: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) =\n  break_preserve_any (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (sift_items (Alloc.Vec.impl_1__as_slice values));\n  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-permutation-without-indexed-exchange-contract",
    "component": "permutation",
    "original": "without-indexed-exchange-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.sift_preserves_births",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "indexed_exchange_preserves",
      "before": "let indexed_exchange_preserves (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{Prims.l_and (v left <= v right) (v right < Seq.length (Alloc.Vec.impl_1__as_slice values))}) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) left (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) right)))) right (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) left))))) [SMTPat (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) left (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) right)))) right (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) left)))] =\n  exchange_preserves_births values left right;\n  ()\n",
      "after": "let indexed_exchange_preserves (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{Prims.l_and (v left <= v right) (v right < Seq.length (Alloc.Vec.impl_1__as_slice values))}) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) left (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) right)))) right (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) left))))) =\n  exchange_preserves_births values left right;\n  ()\n"
    }
  },
  {
    "name": "delete-permutation-without-break-frame",
    "component": "permutation",
    "original": "without-break-frame",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.sift_preserves_births",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "sift_preserves_births",
      "before": "let sift_preserves_births (values: births) (start: usize) (finish: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) [SMTPat (Native.sift_births values start finish)] =\n  break_preserve_any (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (sift_items (Alloc.Vec.impl_1__as_slice values));\n  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let sift_preserves_births (values: births) (start: usize) (finish: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) [SMTPat (Native.sift_births values start finish)] =\n  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-permutation-skip-sort-count-scope",
    "component": "permutation",
    "original": "skip-sort-count-scope",
    "positive": true,
    "owner": null,
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = xs.to_vec();\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-without-drain-sift-contract",
    "component": "permutation",
    "original": "without-drain-sift-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.drain_step_preserves",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "drain_step_preserves",
      "before": "let drain_step_preserves (original: t_Slice Native.t_BirthId) (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires vector_items original current) (ensures break_keeps (vector_items original) (drain_step len current step)) =\n  let finish = len -! mk_usize 1 -! step in\n  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then\n    begin assert (break_keeps (vector_items original) (drain_step len current step));\n    () end\n  else\n    begin let before = Alloc.Vec.impl_1__as_slice current in\n    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in\n    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in\n    indexed_exchange_preserves current (mk_usize 0) finish;\n    sift_preserves_births swapped (mk_usize 0) finish;\n    assert (break_keeps (vector_items original) (drain_step len current step)) by (\n      Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n      Tactics.prune \"Alloc.Slice.impl__to_vec\";\n      Tactics.smt_sync' 1 1\n    ) end\n",
      "after": "let drain_step_preserves (original: t_Slice Native.t_BirthId) (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires vector_items original current) (ensures break_keeps (vector_items original) (drain_step len current step)) =\n  let finish = len -! mk_usize 1 -! step in\n  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then\n    begin assert (break_keeps (vector_items original) (drain_step len current step));\n    () end\n  else\n    begin let before = Alloc.Vec.impl_1__as_slice current in\n    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in\n    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in\n    indexed_exchange_preserves current (mk_usize 0) finish;\n    assert (break_keeps (vector_items original) (drain_step len current step)) by (\n      Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n      Tactics.prune \"Alloc.Slice.impl__to_vec\";\n      Tactics.prune \"Nickel.EditDeletePermutation.sift_preserves_births\";\n      Tactics.smt_sync' 1 1\n    ) end\n"
    }
  },
  {
    "name": "delete-permutation-without-drain-exchange-contract",
    "component": "permutation",
    "original": "without-drain-exchange-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.drain_step_preserves",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "drain_step_preserves",
      "before": "let drain_step_preserves (original: t_Slice Native.t_BirthId) (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires vector_items original current) (ensures break_keeps (vector_items original) (drain_step len current step)) =\n  let finish = len -! mk_usize 1 -! step in\n  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then\n    begin assert (break_keeps (vector_items original) (drain_step len current step));\n    () end\n  else\n    begin let before = Alloc.Vec.impl_1__as_slice current in\n    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in\n    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in\n    indexed_exchange_preserves current (mk_usize 0) finish;\n    sift_preserves_births swapped (mk_usize 0) finish;\n    assert (break_keeps (vector_items original) (drain_step len current step)) by (\n      Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n      Tactics.prune \"Alloc.Slice.impl__to_vec\";\n      Tactics.smt_sync' 1 1\n    ) end\n",
      "after": "let drain_step_preserves (original: t_Slice Native.t_BirthId) (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires vector_items original current) (ensures break_keeps (vector_items original) (drain_step len current step)) =\n  let finish = len -! mk_usize 1 -! step in\n  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then\n    begin assert (break_keeps (vector_items original) (drain_step len current step));\n    () end\n  else\n    begin let before = Alloc.Vec.impl_1__as_slice current in\n    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in\n    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in\n    sift_preserves_births swapped (mk_usize 0) finish;\n    assert (break_keeps (vector_items original) (drain_step len current step)) by (\n      Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n      Tactics.prune \"Alloc.Slice.impl__to_vec\";\n      Tactics.prune \"Nickel.EditDeletePermutation.indexed_exchange_preserves\";\n      Tactics.smt_sync' 1 1\n    ) end\n"
    }
  },
  {
    "name": "delete-permutation-without-drain-break-frame",
    "component": "permutation",
    "original": "without-drain-break-frame",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.drain_callbacks_preserve",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "drain_callbacks_preserve",
      "before": "let drain_callbacks_preserve (original: t_Slice Native.t_BirthId) (len: usize) : Lemma (ensures forall(inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len). Prims.l_and (vector_items original initial) (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at) ==> vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =\n  let each (inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len) : Lemma (requires (vector_items original initial /\\ (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at))) (ensures vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =\n    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (drain_step_preserves original len));\n    break_preserve_any (mk_usize 0) len (vector_items original);\n    assert (vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) by (\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n      Tactics.prune \"Nickel.EditDeletePermutation.drain_step\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)\n",
      "after": "let drain_callbacks_preserve (original: t_Slice Native.t_BirthId) (len: usize) : Lemma (ensures forall(inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len). Prims.l_and (vector_items original initial) (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at) ==> vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =\n  let each (inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len) : Lemma (requires (vector_items original initial /\\ (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at))) (ensures vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =\n    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (drain_step_preserves original len));\n    assert (vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) by (\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n      Tactics.prune \"Nickel.EditDeletePermutation.drain_step\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)\n"
    }
  },
  {
    "name": "delete-permutation-without-ordered-heap-contract",
    "component": "permutation",
    "original": "without-ordered-heap-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.ordered_preserves_births",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "ordered_preserves_births",
      "before": "let ordered_preserves_births (xs: t_Slice Native.t_BirthId) : Lemma (ensures same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  copy_births_exact xs;\n  heap_preserves_births copied len;\n  drain_preserves_births (Native.heap_births copied len) len;\n  assert (same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let ordered_preserves_births (xs: t_Slice Native.t_BirthId) : Lemma (ensures same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  copy_births_exact xs;\n  drain_preserves_births (Native.heap_births copied len) len;\n  assert (same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.prune \"Nickel.EditDeletePermutation.heap_preserves_births\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  },
  {
    "name": "delete-permutation-without-ordered-drain-contract",
    "component": "permutation",
    "original": "without-ordered-drain-contract",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.ordered_preserves_births",
    "root": "EditDeletePermutation",
    "view": {
      "file": "Nickel.EditDeletePermutation.fst",
      "hash": "cd23fad6a9cd1aadfcaab3f33d6b836d765373d9ef2d96447ecb6fbdcf63709c",
      "scope": "ordered_preserves_births",
      "before": "let ordered_preserves_births (xs: t_Slice Native.t_BirthId) : Lemma (ensures same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  copy_births_exact xs;\n  heap_preserves_births copied len;\n  drain_preserves_births (Native.heap_births copied len) len;\n  assert (same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let ordered_preserves_births (xs: t_Slice Native.t_BirthId) : Lemma (ensures same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  copy_births_exact xs;\n  heap_preserves_births copied len;\n  assert (same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.prune \"Alloc.Slice.impl__to_vec\";\n    Tactics.prune \"Nickel.EditDeletePermutation.drain_preserves_births\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  },
  {
    "name": "delete-permutation-ordered-skips-sort-count-scope",
    "component": "permutation",
    "original": "ordered-skips-sort-count-scope",
    "positive": true,
    "owner": null,
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn ordered_births(",
      "before": "fn ordered_births(xs: &[BirthId]) -> Vec<BirthId> {\n    let values = xs.to_vec();\n    let len = values.len();\n    let values = heap_births(values, len);\n    drain_births(values, len)\n}",
      "after": "fn ordered_births(xs: &[BirthId]) -> Vec<BirthId> { xs.to_vec() }"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-permutation-ordered-copy-drops-input",
    "component": "permutation",
    "original": "ordered-copy-drops-input",
    "positive": false,
    "owner": "Nickel.EditDeletePermutation.ordered_preserves_births",
    "root": "EditDeletePermutation",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn ordered_births(",
      "before": "fn ordered_births(xs: &[BirthId]) -> Vec<BirthId> {\n    let values = xs.to_vec();\n    let len = values.len();\n    let values = heap_births(values, len);\n    drain_births(values, len)\n}",
      "after": "fn ordered_births(xs: &[BirthId]) -> Vec<BirthId> {\n    let values = Vec::new();\n    let len = values.len();\n    let values = heap_births(values, len);\n    drain_births(values, len)\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-short-input-false-positive",
    "component": "duplicate-answer",
    "original": "short-input-false-positive",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return true; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-first-pair-inverted",
    "component": "duplicate-answer",
    "original": "first-pair-inverted",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] != xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-adjacent-ignores-event",
    "component": "duplicate-answer",
    "original": "adjacent-ignores-event",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1].index == ordered[i].index { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-wrong-ordered-input",
    "component": "duplicate-answer",
    "original": "wrong-ordered-input",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(&[xs[0], xs[0]]);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-validator-wrong-delete-input",
    "component": "duplicate-answer",
    "original": "validator-wrong-delete-input",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.distinct_delete_keeps_placement_error",
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn validate_new(",
      "before": "fn validate_new(facts: &[Fact], fact: &Fact) -> Result<(), Error> {\n        // Fact-local checks first: a fact that can never be valid must not be\n        // reported as Missing (a deferral the caller retries) while its\n        // dependencies are absent.\n        validate_scalars(&fact.insert)?;\n        if duplicate_births(&fact.delete) {\n            return Err(invalid(Invalid::DeleteDuplicate));\n        }\n        if fact.insert.is_empty() && fact.gap.is_some() {\n            return Err(invalid(Invalid::PlacementWithoutBirth));\n        }\n        if !fact.insert.is_empty() && fact.gap.is_none() {\n            return Err(invalid(Invalid::Gap));\n        }\n        let selected = crate::event_layer::validate_event(facts, fact, &TEXT_OPS)?;\n        let mut basis = Vec::new();\n        for f in facts.iter() {\n            if has_event(&selected, f.id) {\n                push(&mut basis, f.clone())?;\n            }\n        }\n        let seen = visible(&basis)?;\n        for id in fact.delete.iter() {\n            if !has_birth(&seen, *id) {\n                return Err(invalid(Invalid::DeleteNotVisible));\n            }\n        }\n        if !fact.insert.is_empty() && !matches!(fact.gap,Some(gap) if gap<=seen.len()) {\n            return Err(invalid(Invalid::Gap));\n        }\n        Ok(())\n    }",
      "after": "fn validate_new(facts: &[Fact], fact: &Fact) -> Result<(), Error> {\n        // Fact-local checks first: a fact that can never be valid must not be\n        // reported as Missing (a deferral the caller retries) while its\n        // dependencies are absent.\n        validate_scalars(&fact.insert)?;\n        if duplicate_births(&[BirthId { event: fact.id, index: 0 }, BirthId { event: fact.id, index: 0 }]) {\n            return Err(invalid(Invalid::DeleteDuplicate));\n        }\n        if fact.insert.is_empty() && fact.gap.is_some() {\n            return Err(invalid(Invalid::PlacementWithoutBirth));\n        }\n        if !fact.insert.is_empty() && fact.gap.is_none() {\n            return Err(invalid(Invalid::Gap));\n        }\n        let selected = crate::event_layer::validate_event(facts, fact, &TEXT_OPS)?;\n        let mut basis = Vec::new();\n        for f in facts.iter() {\n            if has_event(&selected, f.id) {\n                push(&mut basis, f.clone())?;\n            }\n        }\n        let seen = visible(&basis)?;\n        for id in fact.delete.iter() {\n            if !has_birth(&seen, *id) {\n                return Err(invalid(Invalid::DeleteNotVisible));\n            }\n        }\n        if !fact.insert.is_empty() && !matches!(fact.gap,Some(gap) if gap<=seen.len()) {\n            return Err(invalid(Invalid::Gap));\n        }\n        Ok(())\n    }"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--test",
      "fact_local_first"
    ]
  },
  {
    "name": "delete-duplicate-answer-without-pair-transport",
    "component": "duplicate-answer",
    "original": "without-pair-transport",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "duplicate_answer_has_original_pair",
      "before": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    Nickel.EditDeletePermutation.ordered_preserves_births xs;\n    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n",
      "after": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    Nickel.EditDeletePermutation.ordered_preserves_births xs;\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n"
    }
  },
  {
    "name": "delete-duplicate-answer-without-count-witness",
    "component": "duplicate-answer",
    "original": "without-count-witness",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.same_births_transports_pair",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "same_births_transports_pair",
      "before": "let same_births_transports_pair (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (Nickel.EditDeletePermutation.same_births before after) (repeated after) ==> repeated before) =\n  let each (i: nat) (j: nat) : Lemma (requires (Nickel.EditDeletePermutation.same_births before after /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length after)) (Seq.index after i == Seq.index after j))) (ensures repeated before) =\n    equal_positions_count after i j;\n    assert (Seq.count (Seq.index after i) before >= 2) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    count_has_equal_positions before (Seq.index after i);\n    assert (repeated before) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n",
      "after": "let same_births_transports_pair (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (Nickel.EditDeletePermutation.same_births before after) (repeated after) ==> repeated before) =\n  let each (i: nat) (j: nat) : Lemma (requires (Nickel.EditDeletePermutation.same_births before after /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length after)) (Seq.index after i == Seq.index after j))) (ensures repeated before) =\n    equal_positions_count after i j;\n    assert (Seq.count (Seq.index after i) before >= 2) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    assert (repeated before) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n"
    }
  },
  {
    "name": "delete-duplicate-answer-without-equal-position-count",
    "component": "duplicate-answer",
    "original": "without-equal-position-count",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.same_births_transports_pair",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "same_births_transports_pair",
      "before": "let same_births_transports_pair (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (Nickel.EditDeletePermutation.same_births before after) (repeated after) ==> repeated before) =\n  let each (i: nat) (j: nat) : Lemma (requires (Nickel.EditDeletePermutation.same_births before after /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length after)) (Seq.index after i == Seq.index after j))) (ensures repeated before) =\n    equal_positions_count after i j;\n    assert (Seq.count (Seq.index after i) before >= 2) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    count_has_equal_positions before (Seq.index after i);\n    assert (repeated before) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n",
      "after": "let same_births_transports_pair (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (Nickel.EditDeletePermutation.same_births before after) (repeated after) ==> repeated before) =\n  let each (i: nat) (j: nat) : Lemma (requires (Nickel.EditDeletePermutation.same_births before after /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length after)) (Seq.index after i == Seq.index after j))) (ensures repeated before) =\n    assert (Seq.count (Seq.index after i) before >= 2) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    count_has_equal_positions before (Seq.index after i);\n    assert (repeated before) by (\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n"
    }
  },
  {
    "name": "delete-duplicate-answer-without-ordered-preservation",
    "component": "duplicate-answer",
    "original": "without-ordered-preservation",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "duplicate_answer_has_original_pair",
      "before": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    Nickel.EditDeletePermutation.ordered_preserves_births xs;\n    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n",
      "after": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.prune \"Nickel.EditDeletePermutation.ordered_preserves_births\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n"
    }
  },
  {
    "name": "delete-duplicate-answer-without-duplicate-contract",
    "component": "duplicate-answer",
    "original": "without-duplicate-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.distinct_delete_keeps_placement_error",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "distinct_delete_keeps_placement_error",
      "before": "let distinct_delete_keeps_placement_error (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\\ Prims.l_not (repeated (Alloc.Vec.impl_1__as_slice fact.f_delete)) /\\ Alloc.Vec.impl_1__is_empty fact.f_insert == true /\\ Core_models.Option.impl__is_some fact.f_gap == true)) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) =\n  duplicate_answer_has_original_pair (Alloc.Vec.impl_1__as_slice fact.f_delete);\n  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let distinct_delete_keeps_placement_error (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\\ Prims.l_not (repeated (Alloc.Vec.impl_1__as_slice fact.f_delete)) /\\ Alloc.Vec.impl_1__is_empty fact.f_insert == true /\\ Core_models.Option.impl__is_some fact.f_gap == true)) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) =\n  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.prune \"Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  },
  {
    "name": "delete-duplicate-answer-without-scan-rule",
    "component": "duplicate-answer",
    "original": "without-scan-rule",
    "positive": false,
    "owner": "Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair",
    "root": "EditDeleteAnswer",
    "view": {
      "file": "Nickel.EditDeleteAnswer.fst",
      "hash": "e2ba5146b58bcdfda7d1af58458f537aec32f1757c52034679bf465a52fcb2bb",
      "scope": "duplicate_answer_has_original_pair",
      "before": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    Nickel.EditDeletePermutation.ordered_preserves_births xs;\n    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n",
      "after": "let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    Nickel.EditDeletePermutation.ordered_preserves_births xs;\n    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);\n    assert (Native.duplicate_births xs == true ==> repeated xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n"
    }
  },
  {
    "name": "delete-duplicate-answer-skip-sort-soundness-scope",
    "component": "duplicate-answer",
    "original": "skip-sort-soundness-scope",
    "positive": true,
    "owner": null,
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = xs.to_vec();\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-duplicate-answer-always-false-soundness-scope",
    "component": "duplicate-answer",
    "original": "always-false-soundness-scope",
    "positive": true,
    "owner": null,
    "root": "EditDeleteAnswer",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool { false }"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-complete-always-false",
    "component": "complete",
    "original": "complete-always-false",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_complete",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool { false }"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-complete-skip-sort",
    "component": "complete",
    "original": "complete-skip-sort",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_complete",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn duplicate_births(",
      "before": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = ordered_births(xs);\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}",
      "after": "fn duplicate_births(xs: &[BirthId]) -> bool {\n    if xs.len() < 2 { return false; }\n    if xs[0] == xs[1] { return true; }\n    let ordered = xs.to_vec();\n    for i in 1..ordered.len() {\n        if i > 0 && i < ordered.len() && ordered[i - 1] == ordered[i] { return true; }\n    }\n    false\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-sift-always-breaks",
    "component": "complete",
    "original": "sift-always-breaks",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.sift_is_model",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn sift_births(",
      "before": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= finish / 2 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child + 1]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = old;\n        root = child;\n    }\n    values\n}",
      "after": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= 0 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child + 1]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = old;\n        root = child;\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-sift-wrong-child-comparison",
    "component": "complete",
    "original": "sift-wrong-child-comparison",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.sift_is_model",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn sift_births(",
      "before": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= finish / 2 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child + 1]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = old;\n        root = child;\n    }\n    values\n}",
      "after": "fn sift_births(mut values: Vec<BirthId>, start: usize, finish: usize) -> Vec<BirthId> {\n    let mut root = start;\n    for _ in 0..(usize::BITS as usize) {\n        if root >= finish / 2 { break; }\n        let mut child = root * 2 + 1;\n        if root >= values.len() || child >= values.len() { break; }\n        if child + 1 < finish && child + 1 < values.len() && birth_lt(values[child], values[child]) {\n            child += 1;\n        }\n        if child >= values.len() || !birth_lt(values[root], values[child]) { break; }\n        let old = values[root];\n        values[root] = values[child];\n        values[child] = old;\n        root = child;\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-heap-wrong-start-argument",
    "component": "complete",
    "original": "heap-wrong-start-argument",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.heap_builds",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn heap_births(",
      "before": "fn heap_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..(len / 2) {\n        if step < len / 2 {\n            values = sift_births(values, len / 2 - 1 - step, len);\n        }\n    }\n    values\n}",
      "after": "fn heap_births(mut values: Vec<BirthId>, len: usize) -> Vec<BirthId> {\n    for step in 0..(len / 2) {\n        if step < len / 2 {\n            values = sift_births(values, step, len);\n        }\n    }\n    values\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-writer-insensitive-comparator",
    "component": "complete",
    "original": "writer-insensitive-comparator",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.order_antisymmetric",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn birth_lt(",
      "before": "fn birth_lt(a: BirthId, b: BirthId) -> bool {\n    event_lt(a.event, b.event) || (a.event == b.event && a.index < b.index)\n}",
      "after": "fn birth_lt(a: BirthId, b: BirthId) -> bool {\n    a.event.counter < b.event.counter || (a.event.counter == b.event.counter && a.index < b.index)\n}"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--lib",
      "delete_duplicate_tests"
    ]
  },
  {
    "name": "delete-complete-validator-uses-empty-delete-list",
    "component": "complete",
    "original": "validator-uses-empty-delete-list",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.repeated_delete_rejected_before_admission",
    "root": "EditDeleteComplete",
    "rust": {
      "hash": "182483e81bccfa6643285e2c875d9deee6dacd0d40fa35d42960f200e7de14a4",
      "scope": "fn validate_new(",
      "before": "fn validate_new(facts: &[Fact], fact: &Fact) -> Result<(), Error> {\n        // Fact-local checks first: a fact that can never be valid must not be\n        // reported as Missing (a deferral the caller retries) while its\n        // dependencies are absent.\n        validate_scalars(&fact.insert)?;\n        if duplicate_births(&fact.delete) {\n            return Err(invalid(Invalid::DeleteDuplicate));\n        }\n        if fact.insert.is_empty() && fact.gap.is_some() {\n            return Err(invalid(Invalid::PlacementWithoutBirth));\n        }\n        if !fact.insert.is_empty() && fact.gap.is_none() {\n            return Err(invalid(Invalid::Gap));\n        }\n        let selected = crate::event_layer::validate_event(facts, fact, &TEXT_OPS)?;\n        let mut basis = Vec::new();\n        for f in facts.iter() {\n            if has_event(&selected, f.id) {\n                push(&mut basis, f.clone())?;\n            }\n        }\n        let seen = visible(&basis)?;\n        for id in fact.delete.iter() {\n            if !has_birth(&seen, *id) {\n                return Err(invalid(Invalid::DeleteNotVisible));\n            }\n        }\n        if !fact.insert.is_empty() && !matches!(fact.gap,Some(gap) if gap<=seen.len()) {\n            return Err(invalid(Invalid::Gap));\n        }\n        Ok(())\n    }",
      "after": "fn validate_new(facts: &[Fact], fact: &Fact) -> Result<(), Error> {\n        // Fact-local checks first: a fact that can never be valid must not be\n        // reported as Missing (a deferral the caller retries) while its\n        // dependencies are absent.\n        validate_scalars(&fact.insert)?;\n        if duplicate_births(&[]) {\n            return Err(invalid(Invalid::DeleteDuplicate));\n        }\n        if fact.insert.is_empty() && fact.gap.is_some() {\n            return Err(invalid(Invalid::PlacementWithoutBirth));\n        }\n        if !fact.insert.is_empty() && fact.gap.is_none() {\n            return Err(invalid(Invalid::Gap));\n        }\n        let selected = crate::event_layer::validate_event(facts, fact, &TEXT_OPS)?;\n        let mut basis = Vec::new();\n        for f in facts.iter() {\n            if has_event(&selected, f.id) {\n                push(&mut basis, f.clone())?;\n            }\n        }\n        let seen = visible(&basis)?;\n        for id in fact.delete.iter() {\n            if !has_birth(&seen, *id) {\n                return Err(invalid(Invalid::DeleteNotVisible));\n            }\n        }\n        if !fact.insert.is_empty() && !matches!(fact.gap,Some(gap) if gap<=seen.len()) {\n            return Err(invalid(Invalid::Gap));\n        }\n        Ok(())\n    }"
    },
    "tests": [
      "test",
      "--offline",
      "--locked",
      "--test",
      "fact_local_first"
    ]
  },
  {
    "name": "delete-complete-without-word-growth",
    "component": "complete",
    "original": "without-word-growth",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.exhausted_sift_completes",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "sift_invariant",
      "before": "let sift_invariant (before: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (at: nat) (state: P.sift_state) : Type0 =\n  Prims.l_and (Prims.l_and (Prims.l_and (base <= v state._1) (Prims.pow2 at <= v state._1 + 1)) (segment_reordering before (Alloc.Vec.impl_1__as_slice state._2) base finish)) (heap_except (Alloc.Vec.impl_1__as_slice state._2) base finish (v state._1))\n",
      "after": "let sift_invariant (before: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (at: nat) (state: P.sift_state) : Type0 =\n  Prims.l_and (Prims.l_and (base <= v state._1) (segment_reordering before (Alloc.Vec.impl_1__as_slice state._2) base finish)) (heap_except (Alloc.Vec.impl_1__as_slice state._2) base finish (v state._1))\n"
    }
  },
  {
    "name": "delete-complete-without-hole-parent-bound",
    "component": "complete",
    "original": "without-hole-parent-bound",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.swap_repairs_hole",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "heap_except",
      "before": "let heap_except (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (hole: nat) : Type0 =\n  Prims.l_and (forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (parent <> hole)) (child_of parent child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent)) (forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (child_of parent hole)) (child_of hole child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent))\n",
      "after": "let heap_except (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (hole: nat) : Type0 =\n  forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (parent <> hole)) (child_of parent child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent)\n"
    }
  },
  {
    "name": "delete-complete-without-native-sift-link",
    "component": "complete",
    "original": "without-native-sift-link",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.sift_restores_heap",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "sift_restores_heap",
      "before": "let sift_restores_heap (values: births) (start: usize) (finish: usize) : Lemma (requires (v finish <= Seq.length (Alloc.Vec.impl_1__as_slice values) /\\ heap_from (Alloc.Vec.impl_1__as_slice values) (v start + 1) (v finish))) (ensures Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) [SMTPat (Native.sift_births values start finish)] =\n  initial_sift_state values start finish;\n  sift_callbacks_complete (Alloc.Vec.impl_1__as_slice values) (v start) finish;\n  assert (sift_post (Alloc.Vec.impl_1__as_slice values) (v start) (v finish) (sift_model values start finish)) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.smt_sync' 1 1\n  );\n  sift_is_model values start finish;\n  assert (Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.prune \"Nickel.EditDeleteHeap.sift_model\";\n    Tactics.prune \"Nickel.EditDeleteHeap.heap_from\";\n    Tactics.prune \"Nickel.EditDeleteHeap.segment_reordering\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let sift_restores_heap (values: births) (start: usize) (finish: usize) : Lemma (requires (v finish <= Seq.length (Alloc.Vec.impl_1__as_slice values) /\\ heap_from (Alloc.Vec.impl_1__as_slice values) (v start + 1) (v finish))) (ensures Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) [SMTPat (Native.sift_births values start finish)] =\n  initial_sift_state values start finish;\n  sift_callbacks_complete (Alloc.Vec.impl_1__as_slice values) (v start) finish;\n  assert (sift_post (Alloc.Vec.impl_1__as_slice values) (v start) (v finish) (sift_model values start finish)) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_cf\";\n    Tactics.smt_sync' 1 1\n  );\n  assert (Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.prune \"Nickel.EditDeleteHeap.sift_model\";\n    Tactics.prune \"Nickel.EditDeleteHeap.heap_from\";\n    Tactics.prune \"Nickel.EditDeleteHeap.segment_reordering\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-complete-without-sift-build-contract",
    "component": "complete",
    "original": "without-sift-build-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.heap_builds",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "heap_builds",
      "before": "let heap_builds (values: births) (len: usize) : Lemma (requires v len == Seq.length (Alloc.Vec.impl_1__as_slice values)) (ensures built_heap len (Native.heap_births values len)) [SMTPat (Native.heap_births values len)] =\n  leaf_suffix (Alloc.Vec.impl_1__as_slice values) (v len / 2) (v len);\n  Nickel.LoopUtil.plain_preserve_any (mk_usize 0) (len /! mk_usize 2) (build_invariant len) (built_heap len);\n  assert (built_heap len (Native.heap_births values len)) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range\";\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let heap_builds (values: births) (len: usize) : Lemma (requires v len == Seq.length (Alloc.Vec.impl_1__as_slice values)) (ensures built_heap len (Native.heap_births values len)) [SMTPat (Native.heap_births values len)] =\n  leaf_suffix (Alloc.Vec.impl_1__as_slice values) (v len / 2) (v len);\n  Nickel.LoopUtil.plain_preserve_any (mk_usize 0) (len /! mk_usize 2) (build_invariant len) (built_heap len);\n  assert (built_heap len (Native.heap_births values len)) by (\n    Tactics.prune \"Rust_primitives.Hax.Folds.fold_range\";\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.prune \"Nickel.EditDeleteHeap.sift_restores_heap\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-complete-without-sift-drain-contract",
    "component": "complete",
    "original": "without-sift-drain-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.drain_step_orders",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "drain_step_orders",
      "before": "let drain_step_orders (len: usize) (current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires drain_invariant len (v at) current) (ensures break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) =\n  let finish = len -! mk_usize 1 -! at in\n  let swapped = P.exchange current (mk_usize 0) finish in\n  drain_swap current len at;\n  sift_restores_heap swapped (mk_usize 0) finish;\n  reordering_keeps_tail (Alloc.Vec.impl_1__as_slice swapped) (Alloc.Vec.impl_1__as_slice (Native.sift_births swapped (mk_usize 0) finish)) (v finish);\n  assert (P.drain_step len current at == Flow.ControlFlow_Continue (Native.sift_births swapped (mk_usize 0) finish)) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.smt_sync' 1 1\n  );\n  assert (break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.prune \"Nickel.EditDeletePermutation.exchange\";\n    Tactics.prune \"Nickel.EditDeletePermutation.drain_step\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let drain_step_orders (len: usize) (current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires drain_invariant len (v at) current) (ensures break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) =\n  let finish = len -! mk_usize 1 -! at in\n  let swapped = P.exchange current (mk_usize 0) finish in\n  drain_swap current len at;\n  reordering_keeps_tail (Alloc.Vec.impl_1__as_slice swapped) (Alloc.Vec.impl_1__as_slice (Native.sift_births swapped (mk_usize 0) finish)) (v finish);\n  assert (P.drain_step len current at == Flow.ControlFlow_Continue (Native.sift_births swapped (mk_usize 0) finish)) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.smt_sync' 1 1\n  );\n  assert (break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) by (\n    Tactics.prune \"Nickel_crdt.Edit.sift_births\";\n    Tactics.prune \"Nickel.EditDeletePermutation.exchange\";\n    Tactics.prune \"Nickel.EditDeletePermutation.drain_step\";\n    Tactics.prune \"Nickel.EditDeleteHeap.sift_restores_heap\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-complete-without-heap-build-contract",
    "component": "complete",
    "original": "without-heap-build-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.ordered_births_sorted",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "ordered_births_sorted",
      "before": "let ordered_births_sorted (xs: t_Slice Native.t_BirthId) : Lemma (ensures sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  heap_builds copied len;\n  assert (built_heap len (Native.heap_births copied len)) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.smt_sync' 1 1\n  );\n  drain_sorts (Native.heap_births copied len) len;\n  assert (sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let ordered_births_sorted (xs: t_Slice Native.t_BirthId) : Lemma (ensures sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  assert (built_heap len (Native.heap_births copied len)) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel.EditDeleteHeap.heap_builds\";\n    Tactics.smt_sync' 1 1\n  );\n  drain_sorts (Native.heap_births copied len) len;\n  assert (sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  },
  {
    "name": "delete-complete-without-drain-sort-contract",
    "component": "complete",
    "original": "without-drain-sort-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteHeap.ordered_births_sorted",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteHeap.fst",
      "hash": "28e05f646a48f1078ddaaf2fd9e1bb2cac6fb53c73aca0630de03b62a62fad56",
      "scope": "ordered_births_sorted",
      "before": "let ordered_births_sorted (xs: t_Slice Native.t_BirthId) : Lemma (ensures sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  heap_builds copied len;\n  assert (built_heap len (Native.heap_births copied len)) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.smt_sync' 1 1\n  );\n  drain_sorts (Native.heap_births copied len) len;\n  assert (sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let ordered_births_sorted (xs: t_Slice Native.t_BirthId) : Lemma (ensures sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =\n  let copied = Alloc.Slice.impl__to_vec xs in\n  let len = Alloc.Vec.impl_1__len copied in\n  heap_builds copied len;\n  assert (built_heap len (Native.heap_births copied len)) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.smt_sync' 1 1\n  );\n  assert (sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (\n    Tactics.prune \"Nickel_crdt.Edit.heap_births\";\n    Tactics.prune \"Nickel_crdt.Edit.drain_births\";\n    Tactics.prune \"Nickel.EditDeleteHeap.drain_sorts\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  },
  {
    "name": "delete-complete-without-sorted-output-contract",
    "component": "complete",
    "original": "without-sorted-output-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_complete",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "duplicate_births_complete",
      "before": "let duplicate_births_complete (xs: t_Slice Native.t_BirthId) : Lemma (ensures A.repeated xs ==> Native.duplicate_births xs == true) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    let after = Alloc.Vec.impl_1__as_slice ordered in\n    P.ordered_preserves_births xs;\n    assert (P.same_births after xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    A.same_births_transports_pair after xs;\n    H.ordered_births_sorted xs;\n    sorted_adjacent_free_disallows_pair after;\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (at: nat) (_: unit) -> adjacent_free_before after at) (fun (_: unit) -> adjacent_free_before after (Seq.length after)) (fun (answer: bool) -> answer == true);\n    assert (A.repeated xs ==> Native.duplicate_births xs == true) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n",
      "after": "let duplicate_births_complete (xs: t_Slice Native.t_BirthId) : Lemma (ensures A.repeated xs ==> Native.duplicate_births xs == true) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    let after = Alloc.Vec.impl_1__as_slice ordered in\n    P.ordered_preserves_births xs;\n    assert (P.same_births after xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    A.same_births_transports_pair after xs;\n    sorted_adjacent_free_disallows_pair after;\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (at: nat) (_: unit) -> adjacent_free_before after at) (fun (_: unit) -> adjacent_free_before after (Seq.length after)) (fun (answer: bool) -> answer == true);\n    assert (A.repeated xs ==> Native.duplicate_births xs == true) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.prune \"Nickel.EditDeleteHeap.ordered_births_sorted\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n"
    }
  },
  {
    "name": "delete-complete-without-preserved-original-counts",
    "component": "complete",
    "original": "without-preserved-original-counts",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_complete",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "duplicate_births_complete",
      "before": "let duplicate_births_complete (xs: t_Slice Native.t_BirthId) : Lemma (ensures A.repeated xs ==> Native.duplicate_births xs == true) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    let after = Alloc.Vec.impl_1__as_slice ordered in\n    P.ordered_preserves_births xs;\n    assert (P.same_births after xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.smt_sync' 1 1\n    );\n    A.same_births_transports_pair after xs;\n    H.ordered_births_sorted xs;\n    sorted_adjacent_free_disallows_pair after;\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (at: nat) (_: unit) -> adjacent_free_before after at) (fun (_: unit) -> adjacent_free_before after (Seq.length after)) (fun (answer: bool) -> answer == true);\n    assert (A.repeated xs ==> Native.duplicate_births xs == true) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n",
      "after": "let duplicate_births_complete (xs: t_Slice Native.t_BirthId) : Lemma (ensures A.repeated xs ==> Native.duplicate_births xs == true) [SMTPat (Native.duplicate_births xs)] =\n  if Seq.length xs >= 2 then\n    begin let ordered = Native.ordered_births xs in\n    let after = Alloc.Vec.impl_1__as_slice ordered in\n    assert (P.same_births after xs) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"FStar.Seq.count\";\n      Tactics.prune \"FStar.Seq.Properties.count\";\n      Tactics.prune \"Nickel.EditDeletePermutation.ordered_preserves_births\";\n      Tactics.smt_sync' 1 1\n    );\n    A.same_births_transports_pair after xs;\n    H.ordered_births_sorted xs;\n    sorted_adjacent_free_disallows_pair after;\n    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (at: nat) (_: unit) -> adjacent_free_before after at) (fun (_: unit) -> adjacent_free_before after (Seq.length after)) (fun (answer: bool) -> answer == true);\n    assert (A.repeated xs ==> Native.duplicate_births xs == true) by (\n      Tactics.prune \"Nickel_crdt.Edit.ordered_births\";\n      Tactics.prune \"Rust_primitives.Hax.Folds.fold_range_return\";\n      Tactics.smt_sync' 1 1\n    ) end\n  else\n    begin () end\n"
    }
  },
  {
    "name": "delete-complete-without-comparator-antisymmetry",
    "component": "complete",
    "original": "without-comparator-antisymmetry",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.sorted_adjacent_free_disallows_pair",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "sorted_adjacent_free_disallows_pair",
      "before": "let sorted_adjacent_free_disallows_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) ==> Prims.l_not (A.repeated xs)) =\n  let each (i: nat) (j: nat) : Lemma (requires (Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length xs)) (Seq.index xs i == Seq.index xs j))) (ensures Prims.l_False) =\n    let next = mk_usize (i + 1) in\n    H.order_antisymmetric (Seq.index xs i) (Seq.index xs (i + 1));\n    assert (Seq.index xs i == Seq.index xs (v next)) by (\n      Tactics.prune \"Nickel_crdt.Edit.birth_lt\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n",
      "after": "let sorted_adjacent_free_disallows_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) ==> Prims.l_not (A.repeated xs)) =\n  let each (i: nat) (j: nat) : Lemma (requires (Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) /\\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length xs)) (Seq.index xs i == Seq.index xs j))) (ensures Prims.l_False) =\n    let next = mk_usize (i + 1) in\n    assert (Seq.index xs i == Seq.index xs (v next)) by (\n      Tactics.prune \"Nickel_crdt.Edit.birth_lt\";\n      Tactics.smt_sync' 1 1\n    ) in\n  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);\n  ()\n"
    }
  },
  {
    "name": "delete-complete-without-sound-answer-contract",
    "component": "complete",
    "original": "without-sound-answer-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_exact",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "duplicate_births_exact",
      "before": "let duplicate_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true <==> A.repeated xs) =\n  A.duplicate_answer_has_original_pair xs;\n  duplicate_births_complete xs;\n  assert (Native.duplicate_births xs == true <==> A.repeated xs) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let duplicate_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true <==> A.repeated xs) =\n  duplicate_births_complete xs;\n  assert (Native.duplicate_births xs == true <==> A.repeated xs) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.prune \"Nickel.EditDeleteAnswer.duplicate_answer_has_original_pair\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-complete-without-complete-answer-contract",
    "component": "complete",
    "original": "without-complete-answer-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.duplicate_births_exact",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "duplicate_births_exact",
      "before": "let duplicate_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true <==> A.repeated xs) =\n  A.duplicate_answer_has_original_pair xs;\n  duplicate_births_complete xs;\n  assert (Native.duplicate_births xs == true <==> A.repeated xs) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.smt_sync' 1 1\n  )\n",
      "after": "let duplicate_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true <==> A.repeated xs) =\n  A.duplicate_answer_has_original_pair xs;\n  assert (Native.duplicate_births xs == true <==> A.repeated xs) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.prune \"Nickel.EditDeleteComplete.duplicate_births_complete\";\n    Tactics.smt_sync' 1 1\n  )\n"
    }
  },
  {
    "name": "delete-complete-without-early-rejection-contract",
    "component": "complete",
    "original": "without-early-rejection-contract",
    "positive": false,
    "owner": "Nickel.EditDeleteComplete.repeated_delete_rejected_before_admission",
    "root": "EditDeleteComplete",
    "view": {
      "file": "Nickel.EditDeleteComplete.fst",
      "hash": "4a82ca60240552c5cb51a3f1e9136e0011a397e4d09933093172f22ab6cd8ecc",
      "scope": "repeated_delete_rejected_before_admission",
      "before": "let repeated_delete_rejected_before_admission (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\\ A.repeated (Alloc.Vec.impl_1__as_slice fact.f_delete))) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) =\n  duplicate_births_complete (Alloc.Vec.impl_1__as_slice fact.f_delete);\n  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.smt_sync' 1 1\n  )",
      "after": "let repeated_delete_rejected_before_admission (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\\ A.repeated (Alloc.Vec.impl_1__as_slice fact.f_delete))) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) =\n  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) by (\n    Tactics.prune \"Nickel_crdt.Edit.duplicate_births\";\n    Tactics.prune \"Nickel.EditDeleteComplete.duplicate_births_complete\";\n    Tactics.smt_sync' 1 1\n  )"
    }
  }
];
