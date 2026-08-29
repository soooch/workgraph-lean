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
| 4 | `WorkGraph/Arena.lean` | §4.4, §4.5 | `users`, `finishedBefore`/`conflict`, canonical allocation lengths and effective alignments, arena assignments with computed arena size/alignment, `Finalizable`/`FeasibleFinalization`; **D10, D12, D16** |
| 5 | `WorkGraph/Reuse.lean`, `WorkGraph/Examples.lean` | §5 | **D14** via `SeqBlock`/`ConcBlock` and one generic confined-users lemma (D6-forward en route, D13 load-bearing); a fully worked two-node chain with a concrete feasible finalization |

## Design decisions (and how they map to the spec)

* **Allocation IDs** (1.1/2.1): `Alloc P K = param P ⊕ prod K` over abstract
  name types; mint names are leaf fields chosen at Instantiate and never
  changed by composition.  Global distinctness of produced IDs is the
  *derived invariant* of 2.4's formation conditions — per-leaf `MintInj`
  plus operand `MintDisjoint` (2.1/D3) — matching the spec's treatment of
  IDs as global names that survive composition unchanged (which D4 relies
  on).

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
  `forget` erasure; `SWF` mirrors `WF` and both directions hold in full:
  a schedule erases to a well-formed term (`SWF.forget_wf`) and *every*
  mode assignment of a well-formed term is a well-formed schedule
  (`WF.swf_of_forget`, the 4.3 ∀-form; `WF.exists_schedule` picks one).

* **Alignments** (1.2/2.1): stored as log₂ exponents — the encoding *is*
  the power-of-two constraint, now load-bearing: it is what makes max = lcm
  and D16's address-alignment soundness go through.

* **Conflict domain** (4.4): spec 4.4 defines `users`/`producer`/
  `finishedBefore`/`conflict` on `buffers(W)` only; the Lean predicates are
  total as a representation choice (σ is totalized as the producer of every
  parameter; an off-term produced ID has no producer witness), and every
  main lemma carries the membership hypotheses that scope it back.

## Main theorems (spec §5 → Lean)

| Spec | Lean |
|---|---|
| D1 output categories exhaustive | `LeafInst.resOut_cases` |
| D2 resolution is a lookup | representational: `res*` are non-recursive definitions; the amortization *is* `rebind` |
| D3 composition closure | `WF.inputs_isParam`, `WF.param_mem_inputs_of_mem_outputs`, `WF.param_mem_inputs_of_mem_buffers`, `WF.param_occurs_iff`, `ThetaFits.inputs_rebind_subset_outputs` (totality of `bind`/`res` holds by type) |
| D4 externality | `ThetaFits.paramDom` (+ `Subst.ParamDom.apply_prod`: produced-valued bindings are never rewritten), `WF.mem_minted_of_prod_mem_buffers`, `WF.prod_mem_buffers_of_mem_minted` — **whole-term (`WF`) form only**; the scoped-subterm statement is recovered compositionally via the `*_rebind` image lemmas, not stated separately |
| D5 unfolded internals | `WF.internal_mkSeries`, `WF.internal_par` |
| D6 locality of deadness | forward direction only: `SWF.users_confined_seriesL`/`users_confined_parL`/`users_confined_parR` (every user of an internal allocation of an arm is an instance of that arm); the converse — open-world exposure of interface members via countercontexts — is not formalized |
| D7 no in-place / unique writer | `SWF.mintsAt_unique`, `SWF.exists_producer` (with 3.1 semantic; "no syntax for a second writer" is structural: `prov` re-exposes untouched) |
| D8 ≺ strict partial order | `SW.prec_irrefl`, `SW.prec_asymm` (transitivity by construction); the linearization embedding is `SW.linRank`/`SW.nodeRank` + `SGen.linRank_lt_linRank`; endpoints: `SW.not_prec_src`, `SW.not_sink_prec`, `SW.src_prec_sink` |
| D9 dataflow respects ≺ | `SWF.producer_prec_consumer`, `producer_prec_sink` |
| D10 node-local disjointness | `SWF.conflict_fresh_input`, `SWF.bind_ne_fresh`; discharged by 4.5: `Assignment.fresh_input_disjoint` and `FeasibleFinalization.fresh_input_disjoint` (per-node input/fresh-output byte disjointness — also the conflict content of the spec's allocation-based ping-pong corollary; the two-buffer counting reading is not separately formalized) |
| D12 interface pinning | `SWF.interface_conflict_iff` (the reduction), `SWF.conflict_interface`, `SWF.conflict_input` (fully pinned), `SWF.interface_not_conflict_of_finishedBefore` (an interface output may reuse space wholly finished before its producer), `SWF.conflict_interface_of_user_not_prec` (nothing placed over it from its producer onward); discharged by 4.5: `Assignment.interface_disjoint` |
| D13 series order exceeds data dependency | load-bearing inside the D14 proofs (the `seriesCross` step orders dead ends too); the ordering clauses themselves are the `SGen` generators |
| D14 reuse legality | sequential: one generic lemma `not_conflict_of_confined` over `SW.SeqBlock` (an ordered arm-block pair anywhere in the schedule; `SeqBlock.cross_sgen` lifts the 4.3 clause through contexts); `SWF.series_not_conflict_internal_fresh` / `par12_…` / `par21_…` are its root-level instantiations, and `SWF.series_reuse_in_conc_context` the contextual acceptance case (`Par_conc(Series(W₁,W₂), V)`); concurrent: `SWF.conc_conflict_of_cross_users` — any two allocations with users on opposite branches of a concurrent Par anywhere in the schedule conflict (via `SW.ConcBlock.not_cross_prec`), with `SWF.conc_conflict_fresh` the root-level fresh/fresh special case |
| D16 alignment soundness | `Assignment.address_aligned`: an arena-aligned base plus the 4.5 offset congruence yields per-allocation address alignment (max = lcm from the log₂ encoding, via `SW.effAlignLog_le_arenaAlignLog`) |

Not formalized (out of scope, faithful to the spec's own scoping): 3.1/3.2
byte-level execution semantics (the model's ordering side is captured by
4.3's `≺` and D9; per §6, evaluation semantics is deliberately undefined,
so D11 stays at the node-local reading), the finalization *algorithm* and
selection policy (§4.5 minimization / D15 NP-hardness — the §6 open
objective), and the emitted-artifact dispatch structure (4.6).  The arena
side is canonical: `SW.allocLen` and `SW.effAlignLog` are *computed* from
the term and parameter declarations (with `SWF.allocLen_prod` tying a
produced ID's length to its unique minting slot, and dominance lemmas for
every declared alignment), an `Assignment` (4.5) consumes them directly,
and arena size/alignment are computed maxima (`Assignment.arenaSize`,
`SW.arenaAlignLog`, seeded per 4.5's `max({0} ∪ …)`/`max({1} ∪ …)`) — so
non-canonical arena metadata is unrepresentable.  `Finalizable`
(structural well-formedness + §3.3 length validity) is `finalize`'s domain
`W_wf` (3.3/4.1), and `FeasibleFinalization = Finalizable + Assignment` is
the bundled object `finalize` returns one of — a length-invalid term
admits no bundle — with the D10/D12 discharge theorems restated on it.
D10/D12/D14/D16 are correctness facts any packer inherits.

## Worked example

`WorkGraph/Examples.lean` builds the two-node copy chain
`Series(Leaf(A), Leaf(B), θ)` (A: `x ↦ fresh t₀`, B: `t₀ ↦ fresh t₁`) and
proves: well-formedness, §3.3 validation, *membership in each component* of
the interface/internal split (`x` an input, `t₁` an output, `t₀` internal —
memberships, not set equalities), A ≺ B (both from the Series clause and
re-derived from dataflow via D9), and the concrete D10/D12 conflicts.  It
also constructs the chain's concrete feasible finalization — `x@0, t₀@16,
t₁@32`, canonical lengths and alignments, computed arena size 48 at
alignment 4 — inhabiting `Assignment` and `FeasibleFinalization` end to end
(non-vacuity for the arena layer; plain `decide` only, no new axioms).
It also pins produced-ID distinctness at formation (1.1/2.1/2.4): a Par
whose two occurrences mint the same produced ID is rejected in every mode
(`not_swf_mint_collision` — a produced-ID collision test; the two positions
are distinct instances by occurrence identity), while two occurrences of
the same primitive signature with disjoint minted IDs compose fine
(`swf_two_instances`).
