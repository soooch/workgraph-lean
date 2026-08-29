# Work Graph Model — Lean 4 Formalization

A staged formalization of the Work Graph Model quasi-formal specification
([`SPEC.md`](./SPEC.md)) in Lean 4 + Mathlib.  Every stage is a
self-contained checkpoint that builds green; there are **no `sorry`s** — all
stated theorems are fully proved (axiom footprint: `propext`,
`Classical.choice`, `Quot.sound` only).

## Building

```sh
# toolchain is pinned by ./lean-toolchain (Lean 4.33.1, Mathlib v4.33.1)
lake exe cache get   # fetch Mathlib's prebuilt cache (once)
lake build
```

## Stages / checkpoints

| Stage | File | Spec sections | Contents |
|---|---|---|---|
| 1 | `WorkGraph/Syntax.lean` | §1, §2.1–2.3, §3.3 | Allocation IDs, node signatures, node instances, work terms, resolution, `inputs`/`outputs`/`buffers`/`internal`, minted-ID sets, validation; D1 and basic sanity theorems |
| 2 | `WorkGraph/Composition.lean` | §2.4 | Substitutions, `rebind`, `ThetaFits`, `mkSeries`, the `WF` inductive of legal formations; **D3, D4, D5** |
| 3 | `WorkGraph/Schedule.lean` | §4.2 (nodes), §4.3 | Schedules (`SW`, Par modes), sentinels σ/τ, the generators of ≺ and its transitive closure; **D7, D8, D9** |
| 4 | `WorkGraph/Arena.lean` | §4.4, §4.5 | `users`, `mayOverlap`, arena assignments, declaration coherence, arena bounds; **D10, D12** |
| 5 | `WorkGraph/Reuse.lean`, `WorkGraph/Examples.lean` | §5 | **D14** (with D6 en route, and D13 load-bearing in the proof); a fully worked two-node chain |

## Design decisions (and how they map to the spec)

* **Allocation IDs** (2.1): `Alloc P K = param P ⊕ prod K` over abstract name
  types.  Global distinctness of produced IDs is a well-formedness invariant
  (`MintDisjoint` at every composition + per-leaf `MintInj`), matching the
  spec's treatment of IDs as global names that survive composition unchanged
  (which D4 relies on).

* **Elaborated terms, eager substitution** (1.1/2.4): terms carry their
  current bindings and θ is formation-time data, not a term field — exactly
  the spec's elaborated presentation.  `series w₁ w₂` stores the *already
  rewritten* right arm, so every ID-set equation of 2.3 holds definitionally
  ("the composite contains the rewritten W₂").  Spec Series formation is the
  smart constructor `W.mkSeries w₁ w₂ θ = W.series w₁ (w₂.rebind θ)`;
  `rebind` applies θ to each binding exactly once, simultaneously, matching
  2.4's "applied once, never iterated" — the eager representation D2 names
  (the semantics fixes only values, not representation).

* **Well-formedness**: the inductive `WF` carves out exactly the terms built
  by the formations of 2.4 — parameter-valued leaf bindings (Instantiate),
  `ThetaFits` (dom(θ) exactly `inputs(W₂)`, range in `outputs(W₁)` — 2.4,
  §6 "Partial θ rejected"), and 2.4's formation-level surface of 2.1's
  global distinctness: the operands of Series and Par mint disjoint
  produced-ID sets (`MintDisjoint`).  Node instances are leaf *occurrences*
  (positions in the SP tree, 1.1) — identity needs no separate machinery;
  what is policed is minted names, pinned by
  `Examples.not_swf_mint_collision` / `Examples.swf_two_instances`.

* **Node instances** (4.3): identified by index into the SP tree's
  left-to-right leaf enumeration; σ/τ are the extra `PNode`s of 4.2.
  A schedule is an `SW` tree (a `W` with a `Mode` on every Par) with
  `forget` erasure; `SWF` mirrors `WF` and both directions hold
  (`SWF.forget_wf`, `WF.exists_schedule`).

* **Alignments** (1.2): stored as log₂ exponents, so power-of-two-ness is
  structural.

## Main theorems (spec §5 → Lean)

| Spec | Lean |
|---|---|
| D1 output categories exhaustive | `LeafInst.resOut_cases` |
| D2 resolution is a lookup | representational: `res*` are non-recursive definitions; the amortization *is* `rebind` |
| D3 composition closure | `WF.inputs_isParam`, `WF.param_mem_inputs_of_mem_outputs`, `WF.param_mem_inputs_of_mem_buffers`, `WF.param_occurs_iff`, `ThetaFits.inputs_rebind_subset_outputs` (totality of `bind`/`res` holds by type) |
| D4 externality | `ThetaFits.paramDom` (+ `Subst.ParamDom.apply_prod`: produced-valued bindings are never rewritten), `WF.mem_minted_of_prod_mem_buffers`, `WF.prod_mem_buffers_of_mem_minted` |
| D5 unfolded internals | `WF.internal_mkSeries`, `WF.internal_par` |
| D6 locality of deadness | forward direction only (every user of an internal allocation of the earlier arm is an instance of that arm), proved inline as the `huser` step of the D14 theorems; the converse — open-world exposure of interface members via countercontexts — is not formalized |
| D7 no in-place / unique writer | `SWF.mintsAt_unique`, `SWF.exists_producer` (with 3.1 semantic; "no syntax for a second writer" is structural: `prov` re-exposes untouched) |
| D8 ≺ strict partial order | `SW.prec_irrefl`, `SW.prec_asymm` (transitivity by construction); the linearization embedding is `SW.linRank`/`SW.nodeRank` + `SGen.linRank_lt_linRank`; endpoints: `SW.not_prec_src`, `SW.not_sink_prec`, `SW.src_prec_sink` |
| D9 dataflow respects ≺ | `SWF.producer_prec_consumer`, `producer_prec_sink` |
| D10 node-local disjointness | `SWF.mayOverlap_fresh_input`, `SWF.bind_ne_fresh`; discharged by 4.5: `Assignment.fresh_input_disjoint` and `FeasibleFinalization.fresh_input_disjoint` (per-node input/fresh-output byte disjointness — also the conflict content of the spec's allocation-based ping-pong corollary; the two-buffer counting reading is not separately formalized) |
| D12 interface pinning | `SWF.interface_mayOverlap_iff` (the reduction), `SWF.mayOverlap_interface`, `SWF.mayOverlap_input` (fully pinned), `SWF.interface_not_mayOverlap_of_finished` (an interface output may reuse space wholly finished before its producer), `SWF.mayOverlap_interface_of_user_not_prec` (nothing placed over it from its producer onward); discharged by 4.5: `Assignment.interface_disjoint` |
| D13 series order exceeds data dependency | load-bearing inside the D14 proofs (the `seriesCross` step orders dead ends too); the ordering clauses themselves are the `SGen` generators |
| D14 reuse legality | `SWF.series_not_mayOverlap_internal_fresh`, `SWF.par12_not_mayOverlap_internal_fresh` and its `seq(2,1)` mirror `SWF.par21_not_mayOverlap_internal_fresh`; concurrent Par: `SWF.conc_mayOverlap_of_cross_users` — any two allocations with users on opposite branches of a concurrent Par *anywhere in the schedule* conflict (via `SW.ConcBlock.not_cross_prec`: ≺ never crosses a concurrent Par, even inside a composite), with `SWF.conc_mayOverlap_fresh` the root-level fresh/fresh special case |

Not formalized (out of scope, faithful to the spec's own scoping): 3.1/3.2
byte-level execution semantics (the model's ordering side is captured by
4.3's `≺` and D9; extensionality D11 would need a denotational layer), the
finalization *algorithm* and selection policy (§4.5 minimization / D15
NP-hardness — the §6 open objective), and the emitted-artifact ABI
(4.6/4.7).  `Finalizable` (structural well-formedness + §3.3 length
validity) is the formal counterpart of `finalize`'s domain `W_wf`
(3.3/4.1), and `FeasibleFinalization` is the bundled object `finalize`
returns one of: a `Finalizable` term with coherent length/alignment
functions (`DeclCoherent`), a 4.5 `Assignment`, and dominating
`ArenaBounds` — only through this bundle do the arena structures attach to
a valid finalization (a length-invalid term admits an `Assignment` but no
`FeasibleFinalization`), and the D10/D12 discharge theorems are restated
on it (`FeasibleFinalization.fresh_input_disjoint` / `.interface_disjoint`).
`Assignment`/`ArenaBounds`/`DeclCoherent` are *conservative feasibility
(dominance) relations* for the §4.5 constraint system — §4.5's exact
effective alignment and arena size/alignment are their least elements, not
separately defined here — and D10/D12/D14 are correctness facts any packer
inherits.

## Worked example

`WorkGraph/Examples.lean` builds the two-node copy chain
`Series(Leaf(A), Leaf(B), θ)` (A: `x ↦ fresh t₀`, B: `t₀ ↦ fresh t₁`) and
proves: well-formedness, §3.3 validation, the interface/internal split
(input `x`, output `t₁`, internal `t₀`), A ≺ B (both from the Series clause
and re-derived from dataflow via D9), and the concrete D10/D12 conflicts.
It also pins produced-ID distinctness at formation (1.1/2.1/2.4): a Par
whose two occurrences mint the same produced ID is rejected in every mode
(`not_swf_mint_collision` — a produced-ID collision test; the two positions
are distinct instances by occurrence identity), while two occurrences of
the same primitive signature with disjoint minted IDs compose fine
(`swf_two_instances`).
