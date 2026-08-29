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

* **Eager substitution** (2.4): `series w₁ w₂` stores the *already rewritten*
  right arm, so every ID-set equation of 2.3 holds definitionally ("the
  composite contains the rewritten W₂").  Spec `Series(W₁, W₂, θ)` is the
  smart constructor `W.mkSeries w₁ w₂ θ = W.series w₁ (w₂.rebind θ)`;
  `rebind` applies θ to each binding exactly once, simultaneously, matching
  2.4's "applied once, never iterated" (cf. D2).

* **Well-formedness**: the inductive `WF` carves out exactly the terms built
  by legal formations — parameter-valued leaf bindings (2.2), `ThetaFits`
  (θ total on `inputs(W₂)`, with codomain `outputs(W₁)`, dom exactly the
  inputs — 2.4, §6 "Partial θ rejected"), mint distinctness (2.1).

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
| D6 locality of deadness | proved inline (the `huser` step) inside the D14 theorems |
| D7 no in-place / unique writer | `SWF.mintsAt_unique`, `SWF.exists_producer` (with 3.1 semantic; "no syntax for a second writer" is structural: `prov` re-exposes untouched) |
| D8 ≺ strict partial order | `SW.prec_irrefl`, `SW.prec_asymm` (transitivity by construction); the linearization embedding is `SW.linRank`/`SW.nodeRank` + `SGen.linRank_lt_linRank`; endpoints: `SW.not_prec_src`, `SW.not_sink_prec`, `SW.src_prec_sink` |
| D9 dataflow respects ≺ | `SWF.producer_prec_consumer`, `producer_prec_sink` |
| D10 node-local disjointness | `SWF.mayOverlap_fresh_input`, `SWF.bind_ne_fresh`; discharged by 4.5: `Assignment.fresh_input_disjoint` (ping-pong) |
| D12 interface pinning | `SWF.interface_mayOverlap_iff` (the reduction), `SWF.mayOverlap_interface`, `SWF.mayOverlap_input` (fully pinned); discharged by 4.5: `Assignment.interface_disjoint` |
| D13 series order exceeds data dependency | load-bearing inside the D14 proofs (the `seriesCross` step orders dead ends too); the ordering clauses themselves are the `SGen` generators |
| D14 reuse legality | `SWF.series_not_mayOverlap_internal_fresh`, `SWF.par12_not_mayOverlap_internal_fresh`, `SWF.conc_mayOverlap_fresh` (+ `SW.conc_prec_side`: ≺ never crosses a concurrent Par) |

Not formalized (out of scope, faithful to the spec's own scoping): 3.1/3.2
byte-level execution semantics (the model's ordering side is captured by
4.3's `≺` and D9; extensionality D11 would need a denotational layer), the
finalization *algorithm* and packing objective (§4.5 minimization / D15
NP-hardness — the §6 open objective), and the emitted-artifact ABI
(4.6/4.7).  `Assignment`/`ArenaBounds`/`DeclCoherent` state exactly the
constraint system such an algorithm must satisfy, and D10/D12/D14 are the
correctness facts any packer inherits.

## Worked example

`WorkGraph/Examples.lean` builds the two-node copy chain
`Series(Leaf(A), Leaf(B), θ)` (A: `x ↦ fresh t₀`, B: `t₀ ↦ fresh t₁`) and
proves: well-formedness, §3.3 validation, the interface/internal split
(input `x`, output `t₁`, internal `t₀`), A ≺ B (both from the Series clause
and re-derived from dataflow via D9), and the concrete D10/D12 conflicts.
