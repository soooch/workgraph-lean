/-
# Work Graph Model — Stage 4: Conflict, arena assignments, D10/D12

Formalizes §4.4 (users, `conflict`) and §4.5 (arena assignments), and
proves:

* **D10** (node-local disjointness): a node's fresh output always conflicts
  with each of its inputs (`SWF.conflict_fresh_input`), so 4.5 forces
  address disjointness (`Assignment.fresh_input_disjoint`) — a node's fresh
  output can never occupy an input's space.  Also the self-consumption
  impossibility `SWF.bind_ne_fresh` (an instance cannot consume its own
  fresh output in a well-formed term).

* **D12** (interface pinning): τ is a user of every interface allocation and
  nothing follows τ, so for interface `a` the first conjunct of
  `conflict(a, ·)` always holds (`SWF.interface_conflict_iff`); two
  interface allocations always conflict (`SWF.conflict_interface`), hence
  are pairwise address-disjoint under any assignment
  (`Assignment.interface_disjoint`) — identical IDs (input passthrough to an
  output) being the one sanctioned coincidence; and an input of `W` conflicts
  with *every* allocation (`SWF.conflict_input`) — fully pinned.

The producer/user sets are the relational `IsProducer`/`IsUser` of Stage 3 /
this file; the sentinels are slotless events participating per 4.2/4.4 (σ
produces the parameters, τ is a user of every interface allocation).
-/
import WorkGraph.Schedule

namespace WorkGraph

variable {P K : Type*}

/-! ## §4.2 Interface allocations -/

/-- `inputs(G) ∪ outputs(G)` (4.2): the allocations τ consumes. -/
def Interface (s : SW P K) : Set (Alloc P K) :=
  s.forget.inputs ∪ s.forget.outputs

theorem interface_subset_buffers {s : SW P K} :
    Interface s ⊆ s.forget.buffers := by
  rintro a (ha | ha)
  · exact s.forget.inputs_subset_buffers ha
  · exact s.forget.outputs_subset_buffers ha

/-! ## §4.4 Users and conflict -/

/-- `users(a)` (4.4): the producer of `a` together with every node holding an
input slot resolving to `a` — σ and τ participating per 4.2 (σ as producer of
parameters; τ consuming every interface allocation). -/
def IsUser (s : SW P K) (a : Alloc P K) (n : PNode) : Prop :=
  IsProducer s a n
  ∨ (∃ i, n = .inst i ∧ ConsumesAt s i a)
  ∨ (n = .sink ∧ a ∈ Interface s)

theorem IsProducer.isUser {s : SW P K} {a : Alloc P K} {n : PNode}
    (h : IsProducer s a n) : IsUser s a n := Or.inl h

/-- `finishedBefore(a, b)` (4.4): every user of `a` — producer, consumers,
and τ when `a` is interface — precedes `b`'s producer. -/
def FinishedBefore (s : SW P K) (a b : Alloc P K) : Prop :=
  ∀ n, IsUser s a n → ∀ m, IsProducer s b m → s.Prec n m

/-- `conflict(a, b)` (4.4): neither allocation is fully finished — producer
and all consumers — before the other's producer starts.  Conflicting
allocations must be address-disjoint (4.5).

Domain note: spec 4.4 defines `users`/`producer`/`finishedBefore`/`conflict`
for `a, b ∈ buffers(W)` only.  The Lean predicates are total as a
representation choice — `IsProducer` totalizes σ as the producer of *every*
parameter, and an off-term produced ID simply has no producer witness — and
every main lemma carries the membership hypotheses that scope it back to
`buffers(W)`. -/
def Conflict (s : SW P K) (a b : Alloc P K) : Prop :=
  ¬ FinishedBefore s a b ∧ ¬ FinishedBefore s b a

theorem Conflict.symm {s : SW P K} {a b : Alloc P K}
    (h : Conflict s a b) : Conflict s b a :=
  ⟨h.2, h.1⟩

/-! ## D10: node-local disjointness -/

/-- In a well-formed schedule, an instance never consumes its own fresh
output (D9 + irreflexivity of ≺). -/
theorem SWF.bind_ne_fresh {s : SW P K} (hs : SWF s) {i : ℕ}
    {l : LeafInst P K} (hl : s.leaves[i]? = some l) (j : Fin l.sig.nIn)
    {k : Fin l.sig.nOut} (hfresh : l.sig.prov k = none) :
    l.bind j ≠ .prod (l.mint k) := by
  intro he
  have hc : ConsumesAt s i (.prod (l.mint k)) := ⟨l, hl, ⟨j, he⟩⟩
  have hp : IsProducer s (.prod (l.mint k)) (.inst i) :=
    ⟨i, rfl, l, hl, ⟨k, hfresh, rfl⟩⟩
  exact SW.prec_irrefl s _ (hs.producer_prec_consumer hc hp)

/-- **D10**: a fresh output of a node conflicts with every allocation
resolving to one of the node's input slots.  First conjunct: the node is a
user of the input and the producer of the fresh output, and ≺ is strict
(D8).  Second conjunct: the node is a user of its fresh output, and it
cannot precede the input's producer, which precedes it (D9). -/
theorem SWF.conflict_fresh_input {s : SW P K} (hs : SWF s) {i : ℕ}
    {l : LeafInst P K} (hl : s.leaves[i]? = some l) (j : Fin l.sig.nIn)
    {k : Fin l.sig.nOut} (hfresh : l.sig.prov k = none) :
    Conflict s (l.bind j) (.prod (l.mint k)) := by
  have hc : ConsumesAt s i (l.bind j) := ⟨l, hl, ⟨j, rfl⟩⟩
  have hp : IsProducer s (.prod (l.mint k)) (.inst i) :=
    ⟨i, rfl, l, hl, ⟨k, hfresh, rfl⟩⟩
  constructor
  · intro hall
    exact SW.prec_irrefl s _
      (hall (.inst i) (Or.inr (Or.inl ⟨i, rfl, hc⟩)) (.inst i) hp)
  · intro hall
    obtain ⟨m, hm⟩ := hs.exists_producer hc.mem_buffers
    exact SW.prec_asymm (hall (.inst i) hp.isUser m hm)
      (hs.producer_prec_consumer hc hm)

/-! ## D12: interface pinning -/

/-- **D12** (reduction): for an interface allocation `a`, τ ∈ users(a) and
nothing satisfies τ ≺ n, so `conflict(a, b)` reduces to its second
conjunct. -/
theorem SWF.interface_conflict_iff {s : SW P K} (hs : SWF s)
    {a b : Alloc P K} (ha : a ∈ Interface s) (hb : b ∈ s.forget.buffers) :
    Conflict s a b ↔ ¬ FinishedBefore s b a := by
  constructor
  · exact And.right
  · intro h2
    refine ⟨fun hall => ?_, h2⟩
    obtain ⟨m, hm⟩ := hs.exists_producer hb
    exact SW.not_sink_prec (hall .sink (Or.inr (Or.inr ⟨rfl, ha⟩)) m hm)

/-- **D12**: two interface allocations always conflict (each has τ among its
users), hence are pairwise address-disjoint under any assignment — except
identical IDs (an input of `W` passed through to an output of `W`), the one
sanctioned coincidence. -/
theorem SWF.conflict_interface {s : SW P K} (hs : SWF s)
    {a b : Alloc P K} (ha : a ∈ Interface s) (hb : b ∈ Interface s) :
    Conflict s a b := by
  rw [hs.interface_conflict_iff ha (interface_subset_buffers hb)]
  intro hall
  obtain ⟨m, hm⟩ := hs.exists_producer (interface_subset_buffers ha)
  exact SW.not_sink_prec (hall .sink (Or.inr (Or.inr ⟨rfl, hb⟩)) m hm)

/-- **D12**: an input of `W` (produced by σ; nothing precedes σ) conflicts
with every allocation occurring in the term — inputs are pinned for the
entire run (the deliberate memory cost of 4.2). -/
theorem SWF.conflict_input {s : SW P K} (hs : SWF s) {a b : Alloc P K}
    (ha : a ∈ s.forget.inputs) (hb : b ∈ s.forget.buffers) :
    Conflict s a b := by
  rw [hs.interface_conflict_iff (Or.inl ha) hb]
  intro hall
  -- a is a parameter (D3), so its producer is σ — and nothing precedes σ
  have hpa : IsProducer s a .src := by
    obtain ⟨p, rfl⟩ := Alloc.isParam_iff.mp (hs.forget_wf.inputs_isParam a ha)
    rfl
  obtain ⟨m, hm⟩ := hs.exists_producer hb
  exact SW.not_prec_src (hall m hm.isUser .src hpa)

/-- **D12** (reuse direction): an interface output may still reuse the space
of an allocation wholly finished — producer and all consumers — before its
own producer starts: such a pair does not conflict.  (Stated for any
interface allocation; for an *input* the hypothesis is unsatisfiable, since
nothing precedes σ — inputs stay fully pinned, `SWF.conflict_input`.) -/
theorem SWF.interface_not_conflict_of_finishedBefore {s : SW P K} (hs : SWF s)
    {a b : Alloc P K} (ha : a ∈ Interface s) (hb : b ∈ s.forget.buffers)
    (hfin : FinishedBefore s b a) :
    ¬ Conflict s a b := by
  rw [hs.interface_conflict_iff ha hb]
  exact not_not_intro hfin

/-- **D12** (pinning direction): conversely, nothing may be placed over an
interface allocation from its producer onward — any single user of `b` that
fails to precede `a`'s producer forces the conflict (τ ∈ users(a) forbids
the ordering the other conjunct would need). -/
theorem SWF.conflict_interface_of_user_not_prec {s : SW P K} (hs : SWF s)
    {a b : Alloc P K} {n m : PNode} (ha : a ∈ Interface s)
    (hb : b ∈ s.forget.buffers) (hn : IsUser s b n) (hm : IsProducer s a m)
    (hnp : ¬ s.Prec n m) : Conflict s a b :=
  (hs.interface_conflict_iff ha hb).mpr fun hall => hnp (hall n hn m hm)

/-! ## §4.5 Arena and packing -/

/-- The domain of `finalize` (4.1): `W_wf` — structurally well-formed (2.4,
here a well-formed schedule of one) and length-valid (3.3) relative to the
parameter declarations.  Wherever an assignment is characterized as
belonging to a valid finalization, this is the term-side hypothesis. -/
structure Finalizable (pd : ParamDecl P) (s : SW P K) : Prop where
  swf : SWF s
  lenValid : s.forget.LenValid pd

/-- Byte interval `[offset, offset + len)` membership. -/
def InSpan (offset len x : ℕ) : Prop := offset ≤ x ∧ x < offset + len

/-- An arena *assignment* (4.5), relative to length and effective-alignment
functions on allocation IDs (alignment stored as log₂, 1.2): every
allocation of the term gets an aligned offset, and conflicting allocations
get disjoint byte intervals.  (An empty-length allocation occupies no bytes,
so its interval is disjoint from everything, matching `∩ = ∅` in 4.5.)
By itself this structure does not certify a finalization — that is the
bundled `FeasibleFinalization` below, which ties it to a `Finalizable`
term. -/
structure Assignment (s : SW P K) (len alignLog : Alloc P K → ℕ) where
  offset : Alloc P K → ℕ
  aligned : ∀ a ∈ s.forget.buffers, offset a % 2 ^ alignLog a = 0
  disjoint : ∀ a ∈ s.forget.buffers, ∀ b ∈ s.forget.buffers, a ≠ b →
    Conflict s a b →
    ∀ x, InSpan (offset a) (len a) x → ¬ InSpan (offset b) (len b) x

/-- Arena bounds (4.5/4.6), as a *conservative feasibility (dominance)
relation*: any `size ≥ max (offset + len)` and `alignLog ≥ max alignLog`
qualify.  §4.5's exact arena size and alignment are the least elements of
this relation (`max({0} ∪ …)` / `max({1} ∪ …)`); the emitted artifact takes
those, and minimizing over assignments is the open objective of §6. -/
structure ArenaBounds (s : SW P K) (len alignLog : Alloc P K → ℕ)
    (A : Assignment s len alignLog) (size arenaAlignLog : ℕ) : Prop where
  size_bound : ∀ a ∈ s.forget.buffers, A.offset a + len a ≤ size
  align_bound : ∀ a ∈ s.forget.buffers, alignLog a ≤ arenaAlignLog

/-- Effective lengths/alignments cohere with the declarations (4.5, 3.3):
the length of an allocation is its declared length (parameter declaration or
minting slot declaration), and the alignment function *dominates* the
declared alignment of every declaration-carrying slot resolving to the
allocation — input slots and fresh slots — and, for a parameter, its own
declared alignment, which enters directly: the sentinels carry no slots and
no declarations (4.2), and passthrough slots carry none either.  Like
`ArenaBounds`, this is a conservative feasibility (dominance) relation;
§4.5's *effective alignment* is its least element (the exact max of the
finitely many declarations resolving to the allocation). -/
structure DeclCoherent (pd : ParamDecl P) (s : SW P K)
    (len alignLog : Alloc P K → ℕ) : Prop where
  param_len : ∀ p, Alloc.param p ∈ s.forget.buffers →
    len (.param p) = pd.len p
  param_align : ∀ p, Alloc.param p ∈ s.forget.buffers →
    pd.alignLog p ≤ alignLog (.param p)
  fresh_len : ∀ l ∈ s.leaves, ∀ k : Fin l.sig.nOut, l.sig.prov k = none →
    len (.prod (l.mint k)) = l.sig.freshLen k
  in_align : ∀ l ∈ s.leaves, ∀ j : Fin l.sig.nIn,
    l.sig.inAlignLog j ≤ alignLog (l.bind j)
  fresh_align : ∀ l ∈ s.leaves, ∀ k : Fin l.sig.nOut, l.sig.prov k = none →
    l.sig.freshAlignLog k ≤ alignLog (.prod (l.mint k))

/-- A **feasible finalization** (4.5): the object `finalize` returns one of,
bundled with its validity evidence.  The term lies in `finalize`'s domain
(`Finalizable` = `W_wf`, 3.3/4.1); the length/alignment functions cohere
with the declarations (`DeclCoherent`); the offsets satisfy 4.5
(`Assignment`); and the emitted arena carries dominating bounds
(`ArenaBounds`, 4.6).  The schedule half of the spec's pair (S, assignment)
is `s` itself — an `SW` already carries its Par modes.  Only through this
bundle do the arena structures attach to a valid finalization: none of the
component relations alone certifies one (in particular, a length-invalid
term admits an `Assignment` but no `FeasibleFinalization`). -/
structure FeasibleFinalization (pd : ParamDecl P) (s : SW P K)
    (len alignLog : Alloc P K → ℕ) where
  finalizable : Finalizable pd s
  declCoherent : DeclCoherent pd s len alignLog
  assignment : Assignment s len alignLog
  arenaSize : ℕ
  arenaAlignLog : ℕ
  bounds : ArenaBounds s len alignLog assignment arenaSize arenaAlignLog

/-! ### D10/D12 at the assignment level -/

/-- **D10, discharged by 4.5**: under any valid assignment, a node's fresh
output is address-disjoint from each of its inputs — for positive lengths,
every node's input and fresh-output byte ranges are disjoint. -/
theorem Assignment.fresh_input_disjoint {s : SW P K}
    {len alignLog : Alloc P K → ℕ} (A : Assignment s len alignLog)
    (hs : SWF s) {i : ℕ} {l : LeafInst P K} (hl : s.leaves[i]? = some l)
    (j : Fin l.sig.nIn) {k : Fin l.sig.nOut} (hfresh : l.sig.prov k = none) :
    ∀ x, InSpan (A.offset (l.bind j)) (len (l.bind j)) x →
      ¬ InSpan (A.offset (.prod (l.mint k))) (len (.prod (l.mint k))) x := by
  have hc : ConsumesAt s i (l.bind j) := ⟨l, hl, ⟨j, rfl⟩⟩
  have hbmem : l.bind j ∈ s.forget.buffers := hc.mem_buffers
  have hkmem : Alloc.prod (l.mint k) ∈ s.forget.buffers := by
    apply W.mem_buffers_iff_leaves.mpr
    refine ⟨l, by rw [SW.leaves_forget]; exact List.mem_of_getElem? hl, Or.inr ⟨k, ?_⟩⟩
    unfold LeafInst.resOut
    rw [hfresh]
  exact A.disjoint _ hbmem _ hkmem
    (hs.bind_ne_fresh hl j hfresh)
    (hs.conflict_fresh_input hl j hfresh)

/-- **D12, discharged by 4.5**: under any valid assignment, distinct
interface allocations are pairwise address-disjoint — each is exclusively
and stably placed, as the 4.2 contract demands, regardless of the schedule. -/
theorem Assignment.interface_disjoint {s : SW P K}
    {len alignLog : Alloc P K → ℕ} (A : Assignment s len alignLog)
    (hs : SWF s) {a b : Alloc P K} (ha : a ∈ Interface s)
    (hb : b ∈ Interface s) (hab : a ≠ b) :
    ∀ x, InSpan (A.offset a) (len a) x → ¬ InSpan (A.offset b) (len b) x :=
  A.disjoint _ (interface_subset_buffers ha) _ (interface_subset_buffers hb)
    hab (hs.conflict_interface ha hb)

/-! ### D10/D12 through the feasible-finalization bundle -/

/-- D10 for a feasible finalization: a node's fresh output is byte-disjoint
from each of its inputs. -/
theorem FeasibleFinalization.fresh_input_disjoint {pd : ParamDecl P}
    {s : SW P K} {len alignLog : Alloc P K → ℕ}
    (F : FeasibleFinalization pd s len alignLog) {i : ℕ} {l : LeafInst P K}
    (hl : s.leaves[i]? = some l) (j : Fin l.sig.nIn) {k : Fin l.sig.nOut}
    (hfresh : l.sig.prov k = none) :
    ∀ x, InSpan (F.assignment.offset (l.bind j)) (len (l.bind j)) x →
      ¬ InSpan (F.assignment.offset (.prod (l.mint k)))
          (len (.prod (l.mint k))) x :=
  F.assignment.fresh_input_disjoint F.finalizable.swf hl j hfresh

/-- D12 for a feasible finalization: distinct interface allocations are
byte-disjoint. -/
theorem FeasibleFinalization.interface_disjoint {pd : ParamDecl P}
    {s : SW P K} {len alignLog : Alloc P K → ℕ}
    (F : FeasibleFinalization pd s len alignLog) {a b : Alloc P K}
    (ha : a ∈ Interface s) (hb : b ∈ Interface s) (hab : a ≠ b) :
    ∀ x, InSpan (F.assignment.offset a) (len a) x →
      ¬ InSpan (F.assignment.offset b) (len b) x :=
  F.assignment.interface_disjoint F.finalizable.swf ha hb hab

end WorkGraph
