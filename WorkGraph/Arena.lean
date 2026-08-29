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

/-! ## §4.5 Arena and packing

Canonical arena functions: allocation lengths and effective alignments are
*computed* from the term and the parameter declarations (folds over the leaf
list), the `Assignment` consumes them directly, and arena size/alignment are
computed maxima over the assignment (seeded 0 / exponent 0 = alignment 1,
per 4.5's `max({0} ∪ …)` / `max({1} ∪ …)`) — non-canonical metadata is
unrepresentable.

Note on alignments: they are stored as log₂ exponents throughout
(`alignLog`), so 1.2/2.1's "align is a power of two" is structural — it is
the encoding, which is what makes max = lcm and D16 go through. -/

section FoldMax

variable {α : Type*}

theorem le_foldr_max (f : α → ℕ) {L : List α} {x : α} (hx : x ∈ L) :
    f x ≤ L.foldr (fun y acc => max (f y) acc) 0 := by
  induction L with
  | nil => cases hx
  | cons y L ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih hx).trans (le_max_right _ _)

theorem foldr_max_le {f : α → ℕ} {L : List α} {c : ℕ}
    (h : ∀ x ∈ L, f x ≤ c) : L.foldr (fun y acc => max (f y) acc) 0 ≤ c := by
  induction L with
  | nil => exact Nat.zero_le c
  | cons y L ih =>
      exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

end FoldMax

variable [DecidableEq P] [DecidableEq K]

/-! ### Canonical lengths -/

/-- Length contribution of one leaf to a produced ID: the declared length of
a fresh slot minting `k`, if any (0 otherwise).  Under `SWF`, at most one
slot in the whole term contributes — `SWF.allocLen_prod`. -/
def LeafInst.mintLen (l : LeafInst P K) (k : K) : ℕ :=
  (List.finRange l.sig.nOut).foldr
    (fun i acc =>
      max (if l.sig.prov i = none ∧ l.mint i = k then l.sig.freshLen i else 0)
        acc) 0

def SW.prodLen (s : SW P K) (k : K) : ℕ :=
  s.leaves.foldr (fun l acc => max (l.mintLen k) acc) 0

/-- **Canonical allocation length** (2.1): a parameter's declared length; a
produced ID's minting-slot declared length. -/
def SW.allocLen (pd : ParamDecl P) (s : SW P K) : Alloc P K → ℕ
  | .param p => pd.len p
  | .prod k => s.prodLen k

omit [DecidableEq P] in
@[simp] theorem SW.allocLen_param (pd : ParamDecl P) (s : SW P K) (p : P) :
    s.allocLen pd (.param p) = pd.len p := rfl

omit [DecidableEq P] [DecidableEq K] in
/-- Every leaf of a well-formed schedule has injective minting. -/
theorem SWF.mintInj_of_mem {s : SW P K} (hs : SWF s) :
    ∀ {l : LeafInst P K}, l ∈ s.leaves → l.MintInj := by
  induction hs with
  | @leaf l₀ hβ hm =>
      intro l hl
      rw [SW.leaves_leaf, List.mem_singleton] at hl
      subst hl
      exact hm
  | @series s₁ s₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro l hl
      rw [SW.leaves_series, List.mem_append] at hl
      rcases hl with hl | hl
      · exact ih₁ hl
      · rw [SW.leaves_rebind, List.mem_map] at hl
        obtain ⟨l₀, hl₀, rfl⟩ := hl
        have h : l₀.MintInj := ih₂ hl₀
        exact h
  | @par m s₁ s₂ h₁ h₂ hd ih₁ ih₂ =>
      intro l hl
      rw [SW.leaves_par, List.mem_append] at hl
      rcases hl with hl | hl
      · exact ih₁ hl
      · exact ih₂ hl

omit [DecidableEq P] in
/-- **Canonical length agrees with the minting slot** (2.1): under `SWF`,
`allocLen` of a produced ID is exactly the `freshLen` declared where it is
minted — D7 uniqueness makes the fold's single contribution the max. -/
theorem SWF.allocLen_prod {pd : ParamDecl P} {s : SW P K} (hs : SWF s)
    {i : ℕ} {l : LeafInst P K} (hl : s.leaves[i]? = some l)
    {k : Fin l.sig.nOut} (hfresh : l.sig.prov k = none) :
    s.allocLen pd (.prod (l.mint k)) = l.sig.freshLen k := by
  have hmem : l ∈ s.leaves := List.mem_of_getElem? hl
  apply le_antisymm
  · apply foldr_max_le
    intro l' hl'
    apply foldr_max_le
    intro i' hi'
    split
    · rename_i hcond
      -- l' mints (l.mint k) at fresh slot i': by D7 uniqueness, l' = l and,
      -- by per-leaf injectivity, i' = k
      obtain ⟨i₁, hi₁⟩ := List.mem_iff_getElem?.mp hl'
      have hm₁ : MintsAt s i₁ (l.mint k) := ⟨l', hi₁, ⟨i', hcond.1, hcond.2⟩⟩
      have hm₀ : MintsAt s i (l.mint k) := ⟨l, hl, ⟨k, hfresh, rfl⟩⟩
      have : i₁ = i := hs.mintsAt_unique hm₁ hm₀
      subst this
      have : l' = l := by
        rw [hl] at hi₁
        exact (Option.some.inj hi₁).symm
      subst this
      have : i' = k := hs.mintInj_of_mem hmem i' k hcond.1 hfresh hcond.2
      subst this
      exact le_refl _
    · exact Nat.zero_le _
  · refine le_trans ?_ (le_foldr_max (fun l' => l'.mintLen (l.mint k)) hmem)
    refine le_trans ?_
      (le_foldr_max
        (fun i' => if l.sig.prov i' = none ∧ l.mint i' = l.mint k then
          l.sig.freshLen i' else 0)
        (List.mem_finRange k))
    rw [if_pos ⟨hfresh, rfl⟩]

/-! ### Canonical effective alignment -/

/-- Alignment-exponent contribution of one leaf to an allocation: the max
declared alignment over its input slots binding `a` and fresh slots minting
`a` (passthrough slots carry no declarations — 1.2). -/
def LeafInst.alignContrib (l : LeafInst P K) (a : Alloc P K) : ℕ :=
  max
    ((List.finRange l.sig.nIn).foldr
      (fun j acc => max (if l.bind j = a then l.sig.inAlignLog j else 0) acc)
      0)
    ((List.finRange l.sig.nOut).foldr
      (fun i acc =>
        max (if l.sig.prov i = none ∧ Alloc.prod (l.mint i) = a then
          l.sig.freshAlignLog i else 0) acc) 0)

/-- **Effective alignment** (4.5), exponent form: exactly the max of the
declared alignments of every slot resolving to the allocation and, for a
parameter, its own declared alignment ("σ carries no slots, so the
parameter's declaration enters directly"). -/
def SW.effAlignLog (pd : ParamDecl P) (s : SW P K) (a : Alloc P K) : ℕ :=
  max
    (match a with
      | .param p => pd.alignLog p
      | .prod _ => 0)
    (s.leaves.foldr (fun l acc => max (l.alignContrib a) acc) 0)

/-- The effective alignment dominates every input-slot declaration resolving
to the allocation. -/
theorem SW.inAlignLog_le_effAlignLog (pd : ParamDecl P) {s : SW P K}
    {l : LeafInst P K} (hl : l ∈ s.leaves) (j : Fin l.sig.nIn) :
    l.sig.inAlignLog j ≤ s.effAlignLog pd (l.bind j) := by
  refine le_trans (le_trans ?_ (le_max_left _ _))
    (le_trans (le_foldr_max (fun l' => l'.alignContrib (l.bind j)) hl)
      (le_max_right _ _))
  refine le_trans ?_
    (le_foldr_max
      (fun j' => if l.bind j' = l.bind j then l.sig.inAlignLog j' else 0)
      (List.mem_finRange j))
  rw [if_pos rfl]

/-- The effective alignment dominates every fresh-slot declaration minting
the allocation. -/
theorem SW.freshAlignLog_le_effAlignLog (pd : ParamDecl P) {s : SW P K}
    {l : LeafInst P K} (hl : l ∈ s.leaves) {k : Fin l.sig.nOut}
    (hfresh : l.sig.prov k = none) :
    l.sig.freshAlignLog k ≤ s.effAlignLog pd (.prod (l.mint k)) := by
  refine le_trans (le_trans ?_ (le_max_right _ _))
    (le_trans
      (le_foldr_max (fun l' => l'.alignContrib (.prod (l.mint k))) hl)
      (le_max_right _ _))
  refine le_trans ?_
    (le_foldr_max
      (fun i' => if l.sig.prov i' = none ∧ Alloc.prod (l.mint i') = .prod (l.mint k) then
        l.sig.freshAlignLog i' else 0)
      (List.mem_finRange k))
  rw [if_pos ⟨hfresh, rfl⟩]

/-- The effective alignment of a parameter dominates its own declaration. -/
theorem SW.paramAlignLog_le_effAlignLog (pd : ParamDecl P) (s : SW P K)
    (p : P) : pd.alignLog p ≤ s.effAlignLog pd (.param p) :=
  le_max_left _ _

/-! ### Enumerating `buffers(W)` -/

/-- All resolved slots of one instance. -/
def LeafInst.allocs (l : LeafInst P K) : List (Alloc P K) :=
  (List.finRange l.sig.nIn).map l.bind ++
    (List.finRange l.sig.nOut).map l.resOut

/-- `buffers(W)` (2.3), as a list. -/
def SW.allocList (s : SW P K) : List (Alloc P K) :=
  s.leaves.flatMap LeafInst.allocs

omit [DecidableEq P] [DecidableEq K] in
theorem SW.mem_allocList_iff {s : SW P K} {a : Alloc P K} :
    a ∈ s.allocList ↔ a ∈ s.forget.buffers := by
  rw [SW.allocList, List.mem_flatMap, W.mem_buffers_iff_leaves]
  simp only [SW.leaves_forget]
  constructor
  · rintro ⟨l, hl, ha⟩
    refine ⟨l, hl, ?_⟩
    rw [LeafInst.allocs, List.mem_append, List.mem_map, List.mem_map] at ha
    rcases ha with ⟨j, -, rfl⟩ | ⟨kk, -, rfl⟩
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨kk, rfl⟩
  · rintro ⟨l, hl, ha⟩
    refine ⟨l, hl, ?_⟩
    rw [LeafInst.allocs, List.mem_append, List.mem_map, List.mem_map]
    rcases ha with ⟨j, rfl⟩ | ⟨kk, rfl⟩
    · exact Or.inl ⟨j, List.mem_finRange j, rfl⟩
    · exact Or.inr ⟨kk, List.mem_finRange kk, rfl⟩

/-! ### The domain of `finalize`, assignments, and the emitted arena -/

/-- The domain of `finalize` (4.1): `W_wf` — structurally well-formed (2.4,
here a well-formed schedule of one) and length-valid (3.3) relative to the
parameter declarations. -/
structure Finalizable (pd : ParamDecl P) (s : SW P K) : Prop where
  swf : SWF s
  lenValid : s.forget.LenValid pd

/-- Byte interval `[offset, offset + len)` membership. -/
def InSpan (offset len x : ℕ) : Prop := offset ≤ x ∧ x < offset + len

/-- An arena *assignment* (4.5) over the canonical lengths and effective
alignments: every allocation of the term gets an aligned offset, and
conflicting allocations get disjoint byte intervals.  (An empty-length
allocation occupies no bytes, so its interval is disjoint from everything,
matching `∩ = ∅` in 4.5.) -/
structure Assignment (pd : ParamDecl P) (s : SW P K) where
  offset : Alloc P K → ℕ
  aligned : ∀ a ∈ s.forget.buffers, offset a % 2 ^ s.effAlignLog pd a = 0
  disjoint : ∀ a ∈ s.forget.buffers, ∀ b ∈ s.forget.buffers, a ≠ b →
    Conflict s a b →
    ∀ x, InSpan (offset a) (s.allocLen pd a) x →
      ¬ InSpan (offset b) (s.allocLen pd b) x

/-- Arena size (4.5): `max({0} ∪ { offset(a) + len(a) })` — computed. -/
def Assignment.arenaSize {pd : ParamDecl P} {s : SW P K}
    (A : Assignment pd s) : ℕ :=
  s.allocList.foldr (fun a acc => max (A.offset a + s.allocLen pd a) acc) 0

/-- Arena alignment exponent (4.5): `max({1} ∪ { align(a) })`, i.e. exponent
`max({0} ∪ { alignLog(a) })` — computed, assignment-independent. -/
def SW.arenaAlignLog (pd : ParamDecl P) (s : SW P K) : ℕ :=
  s.allocList.foldr (fun a acc => max (s.effAlignLog pd a) acc) 0

theorem Assignment.le_arenaSize {pd : ParamDecl P} {s : SW P K}
    (A : Assignment pd s) {a : Alloc P K} (ha : a ∈ s.forget.buffers) :
    A.offset a + s.allocLen pd a ≤ A.arenaSize := by
  unfold Assignment.arenaSize
  exact le_foldr_max (fun a => A.offset a + s.allocLen pd a)
    (SW.mem_allocList_iff.mpr ha)

theorem SW.effAlignLog_le_arenaAlignLog {pd : ParamDecl P} {s : SW P K}
    {a : Alloc P K} (ha : a ∈ s.forget.buffers) :
    s.effAlignLog pd a ≤ s.arenaAlignLog pd := by
  unfold SW.arenaAlignLog
  exact le_foldr_max (fun a => s.effAlignLog pd a)
    (SW.mem_allocList_iff.mpr ha)

/-- **D16 (alignment soundness)**: every alignment is a power of two (the
log₂ encoding), so divisibility totally orders them and max = lcm — a base
address aligned to the arena alignment is aligned for every allocation:
`base + offset(a) ≡ 0 (mod align(a))`, which is what makes 4.5's maxima
sufficient for the ABI (4.7). -/
theorem Assignment.address_aligned {pd : ParamDecl P} {s : SW P K}
    (A : Assignment pd s) {base : ℕ}
    (hbase : base % 2 ^ s.arenaAlignLog pd = 0) {a : Alloc P K}
    (ha : a ∈ s.forget.buffers) :
    (base + A.offset a) % 2 ^ s.effAlignLog pd a = 0 := by
  have hdvd : (2 : ℕ) ^ s.effAlignLog pd a ∣ 2 ^ s.arenaAlignLog pd :=
    Nat.pow_dvd_pow 2 (SW.effAlignLog_le_arenaAlignLog ha)
  have h1 : (2 : ℕ) ^ s.effAlignLog pd a ∣ base :=
    Nat.dvd_trans hdvd (Nat.dvd_of_mod_eq_zero hbase)
  have h2 : (2 : ℕ) ^ s.effAlignLog pd a ∣ A.offset a :=
    Nat.dvd_of_mod_eq_zero (A.aligned a ha)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add h1 h2)

/-- A **feasible finalization** (4.5): the term lies in `finalize`'s domain
(`Finalizable` = `W_wf`) together with an assignment over the canonical
lengths and effective alignments.  The schedule half of the spec's pair
(S, assignment) is `s` itself; arena size and alignment are computed from
the assignment, so non-canonical metadata is unrepresentable — a
length-invalid term admits no bundle, and an allocation-free term gets the
computed size 0 / alignment 2⁰ = 1 of 4.5. -/
structure FeasibleFinalization (pd : ParamDecl P) (s : SW P K) where
  finalizable : Finalizable pd s
  assignment : Assignment pd s

/-! ### D10/D12 at the assignment level -/

/-- **D10, discharged by 4.5**: under any valid assignment, a node's fresh
output is address-disjoint from each of its inputs — for positive lengths,
every node's input and fresh-output byte ranges are disjoint. -/
theorem Assignment.fresh_input_disjoint {pd : ParamDecl P} {s : SW P K}
    (A : Assignment pd s) (hs : SWF s) {i : ℕ} {l : LeafInst P K}
    (hl : s.leaves[i]? = some l) (j : Fin l.sig.nIn) {k : Fin l.sig.nOut}
    (hfresh : l.sig.prov k = none) :
    ∀ x, InSpan (A.offset (l.bind j)) (s.allocLen pd (l.bind j)) x →
      ¬ InSpan (A.offset (.prod (l.mint k)))
          (s.allocLen pd (.prod (l.mint k))) x := by
  have hc : ConsumesAt s i (l.bind j) := ⟨l, hl, ⟨j, rfl⟩⟩
  have hbmem : l.bind j ∈ s.forget.buffers := hc.mem_buffers
  have hkmem : Alloc.prod (l.mint k) ∈ s.forget.buffers := by
    apply W.mem_buffers_iff_leaves.mpr
    refine ⟨l, by rw [SW.leaves_forget]; exact List.mem_of_getElem? hl,
      Or.inr ⟨k, ?_⟩⟩
    unfold LeafInst.resOut
    rw [hfresh]
  exact A.disjoint _ hbmem _ hkmem
    (hs.bind_ne_fresh hl j hfresh)
    (hs.conflict_fresh_input hl j hfresh)

/-- **D12, discharged by 4.5**: under any valid assignment, distinct
interface allocations are pairwise address-disjoint — each is exclusively
and stably placed, as 4.2's contract demands, regardless of the schedule. -/
theorem Assignment.interface_disjoint {pd : ParamDecl P} {s : SW P K}
    (A : Assignment pd s) (hs : SWF s) {a b : Alloc P K}
    (ha : a ∈ Interface s) (hb : b ∈ Interface s) (hab : a ≠ b) :
    ∀ x, InSpan (A.offset a) (s.allocLen pd a) x →
      ¬ InSpan (A.offset b) (s.allocLen pd b) x :=
  A.disjoint _ (interface_subset_buffers ha) _ (interface_subset_buffers hb)
    hab (hs.conflict_interface ha hb)

/-! ### D10/D12 through the feasible-finalization bundle -/

/-- D10 for a feasible finalization. -/
theorem FeasibleFinalization.fresh_input_disjoint {pd : ParamDecl P}
    {s : SW P K} (F : FeasibleFinalization pd s) {i : ℕ} {l : LeafInst P K}
    (hl : s.leaves[i]? = some l) (j : Fin l.sig.nIn) {k : Fin l.sig.nOut}
    (hfresh : l.sig.prov k = none) :
    ∀ x, InSpan (F.assignment.offset (l.bind j))
        (s.allocLen pd (l.bind j)) x →
      ¬ InSpan (F.assignment.offset (.prod (l.mint k)))
          (s.allocLen pd (.prod (l.mint k))) x :=
  F.assignment.fresh_input_disjoint F.finalizable.swf hl j hfresh

/-- D12 for a feasible finalization. -/
theorem FeasibleFinalization.interface_disjoint {pd : ParamDecl P}
    {s : SW P K} (F : FeasibleFinalization pd s) {a b : Alloc P K}
    (ha : a ∈ Interface s) (hb : b ∈ Interface s) (hab : a ≠ b) :
    ∀ x, InSpan (F.assignment.offset a) (s.allocLen pd a) x →
      ¬ InSpan (F.assignment.offset b) (s.allocLen pd b) x :=
  F.assignment.interface_disjoint F.finalizable.swf ha hb hab

end WorkGraph
