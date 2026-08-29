/-
# Work Graph Model — Stage 1: Syntax, allocations, resolution, ID-set functions

Formalizes §1 (syntax), §2.1–2.3 (allocation IDs, binding/resolution, ID-set
functions) and §3.3 (validation) of `SPEC.md`.

Representation notes (design decisions, cross-checked against the spec):

* Allocation IDs (`Alloc`) are a sum of an abstract parameter type `P` (𝔸_π)
  and an abstract produced-ID name type `K` (𝔸_★).  Mint names are fields of
  leaves (1.1), chosen at Instantiate and never changed by composition;
  global distinctness of produced IDs is a *derived invariant* of 2.4's
  formation conditions — per-leaf injectivity (`MintInj`) plus operand mint
  disjointness (`MintDisjoint`), see spec 2.1/D3 — matching the spec's
  treatment of IDs as global names that survive composition unchanged
  (needed for D4).

* We use the *eager* representation of composition (2.4): the term
  `W.series w₁ w₂` stores the **already-rewritten** right arm, so the ID-set
  equations of 2.3 hold definitionally ("the composite contains the rewritten
  W₂; every function of 2.3 reads current bindings").  The substitution θ and
  the act of rewriting are Stage 2 (`Subst`, `rebind`, `W.mkSeries`).

* Slot names: the spec's finite named slot sets are represented by `Fin n`
  (a canonical finite naming); nothing in the model depends on the names.

* `align` is a power of two (1.2); we store the exponent (`alignLog`),
  making power-of-two-ness structural.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

namespace WorkGraph

/-! ## §2.1 Allocation IDs: 𝔸 = 𝔸_★ ⊎ 𝔸_π -/

/-- An allocation ID (2.1): either a *parameter* (𝔸_π, a free variable of the
open term, standing for an externally produced buffer) or a *produced* ID
(𝔸_★, minted by a fresh output slot of some node instance). -/
inductive Alloc (P K : Type*) where
  | param : P → Alloc P K
  | prod : K → Alloc P K
  deriving DecidableEq

namespace Alloc

variable {P K : Type*}

/-- The set of parameter-valued allocation IDs. -/
def IsParam : Alloc P K → Prop
  | .param _ => True
  | .prod _ => False

@[simp] theorem isParam_param (p : P) : (Alloc.param (K := K) p).IsParam := trivial
@[simp] theorem not_isParam_prod (k : K) : ¬ (Alloc.prod (P := P) k).IsParam := id

theorem isParam_iff {a : Alloc P K} : a.IsParam ↔ ∃ p, a = .param p := by
  cases a <;> simp [IsParam]

end Alloc

/-! ## §1.2 Primitive nodes -/

/-- A primitive node *signature* (1.2): finite sets of input and output slots,
a provenance declaration, and `(len, align)` declarations for input slots and
fresh output slots.

`prov k = none` is the spec's `prov_N(outₖ) = ★` (a **fresh** slot, minting a
new allocation); `prov k = some j` re-exposes, untouched, the allocation
bound to input slot `j` (a **passthrough** slot).

`freshLen`/`freshAlignLog` are total over output slots for convenience; their
values are *meaningful only on fresh slots* — passthrough slots "carry only
their `prov` pointer, no declarations of their own" (1.2), and no definition
below ever reads `freshLen`/`freshAlignLog` at a passthrough slot. -/
structure NodeSig where
  nIn : ℕ
  nOut : ℕ
  prov : Fin nOut → Option (Fin nIn)
  inLen : Fin nIn → ℕ
  inAlignLog : Fin nIn → ℕ
  freshLen : Fin nOut → ℕ
  freshAlignLog : Fin nOut → ℕ

/-- A leaf description: a signature together with its current binding `bind`
(1.1/2.2) and its mint names (1.1: an injection from the ★ slots into 𝔸_★,
chosen at Instantiate and never changed by composition).  In a standalone
leaf the binding is parameter-valued (2.4, Instantiate — enforced by `WF` in
Stage 2); interior leaves of a composite may carry produced-valued bindings
installed by Series substitution (2.4).  `mint` is total over output slots
for convenience; it is *read only at fresh slots*, and injectivity on fresh
slots is the `MintInj` condition of 2.4. -/
structure LeafInst (P K : Type*) where
  sig : NodeSig
  bind : Fin sig.nIn → Alloc P K
  mint : Fin sig.nOut → K

namespace LeafInst

variable {P K : Type*} (l : LeafInst P K)

/-! ### §2.2 Resolution -/

/-- `res(N, inⱼ)` (2.2): an input slot resolves to its binding. -/
def resIn (j : Fin l.sig.nIn) : Alloc P K := l.bind j

/-- `res(N, outₖ)` (2.2): a fresh output slot resolves to its minted ID; a
passthrough slot resolves to the binding of the input it points at. -/
def resOut (k : Fin l.sig.nOut) : Alloc P K :=
  match l.sig.prov k with
  | none => .prod (l.mint k)
  | some j => l.bind j

/-- **D1** (fresh/passthrough are exhaustive): by the type of `prov` every
output slot is exactly one of fresh (resolving to its minted ID) or
passthrough (resolving to a bound input), and nothing restricts which. -/
theorem resOut_cases (k : Fin l.sig.nOut) :
    (l.sig.prov k = none ∧ l.resOut k = .prod (l.mint k)) ∨
    (∃ j, l.sig.prov k = some j ∧ l.resOut k = l.bind j) := by
  unfold resOut
  cases h : l.sig.prov k with
  | none => exact .inl ⟨rfl, rfl⟩
  | some j => exact .inr ⟨j, rfl, rfl⟩

/-! ### Leaf-level ID sets -/

/-- Resolved input IDs of a single node instance. -/
def inputs : Set (Alloc P K) := Set.range l.bind

/-- Resolved output IDs of a single node instance. -/
def outputs : Set (Alloc P K) := Set.range l.resOut

/-- Produced IDs minted by this instance: one per **fresh** output slot. -/
def minted : Set K := { k | ∃ i, l.sig.prov i = none ∧ l.mint i = k }

/-- Within one leaf, `mint` is injective on fresh slots (2.4, Instantiate;
together with operand mint disjointness this yields 2.1's
global-distinctness invariant — D3). -/
def MintInj : Prop :=
  ∀ i i', l.sig.prov i = none → l.sig.prov i' = none →
    l.mint i = l.mint i' → i = i'

theorem mem_inputs {a : Alloc P K} : a ∈ l.inputs ↔ ∃ j, l.bind j = a :=
  Set.mem_range

theorem mem_outputs {a : Alloc P K} : a ∈ l.outputs ↔ ∃ k, l.resOut k = a :=
  Set.mem_range

/-- Every output is a minted ID or a re-exposed input: a leaf's outputs are
contained in its minted IDs together with its inputs. -/
theorem outputs_subset :
    l.outputs ⊆ (Alloc.prod '' l.minted) ∪ l.inputs := by
  rintro a ⟨k, rfl⟩
  rcases l.resOut_cases k with ⟨h, hres⟩ | ⟨j, _, hres⟩
  · exact Or.inl ⟨l.mint k, ⟨k, h, rfl⟩, hres.symm⟩
  · exact Or.inr ⟨j, hres.symm⟩

end LeafInst

/-! ## §1.1 Work terms -/

/-- Work terms (1.1, verbatim):
`W ::= Leaf(N, bind, mint) | Series(W₁, W₂) | Par(W₁, W₂)` — elaborated
objects carrying current bindings and mint names; β and θ are formation-time
data, not fields of terms.

The term tree is the *SP tree*.  The `series` constructor stores the right
arm with the Series substitution **already applied** to its bindings ("the
composite contains the rewritten W₂", 2.4).  Formation syntax: Series
formation with a given θ is the smart constructor `W.mkSeries` of Stage 2
(`w₁.mkSeries w₂ θ = W.series w₁ (w₂.rebind θ)`), and terms built only by
the formations of 2.4 are carved out by `WF` (Stage 2). -/
inductive W (P K : Type*) where
  | leaf (l : LeafInst P K)
  | series (w₁ w₂ : W P K)
  | par (w₁ w₂ : W P K)

namespace W

variable {P K : Type*}

/-! ### §2.3 ID-set functions (verbatim: the eager representation makes each
equation of 2.3 a definitional clause) -/

/-- `inputs : W → 𝒫(𝔸)` (2.3). -/
def inputs : W P K → Set (Alloc P K)
  | .leaf l => l.inputs
  | .series w₁ _ => w₁.inputs
  | .par w₁ w₂ => w₁.inputs ∪ w₂.inputs

/-- `outputs : W → 𝒫(𝔸)` (2.3). -/
def outputs : W P K → Set (Alloc P K)
  | .leaf l => l.outputs
  | .series _ w₂ => w₂.outputs
  | .par w₁ w₂ => w₁.outputs ∪ w₂.outputs

/-- `buffers : W → 𝒫(𝔸)` (2.3). -/
def buffers : W P K → Set (Alloc P K)
  | .leaf l => l.inputs ∪ l.outputs
  | .series w₁ w₂ => w₁.buffers ∪ w₂.buffers
  | .par w₁ w₂ => w₁.buffers ∪ w₂.buffers

/-- `internal(W) = buffers(W) − inputs(W) − outputs(W)` (2.3). -/
def internal (w : W P K) : Set (Alloc P K) :=
  { a | a ∈ w.buffers ∧ a ∉ w.inputs ∧ a ∉ w.outputs }

theorem mem_internal {w : W P K} {a : Alloc P K} :
    a ∈ w.internal ↔ a ∈ w.buffers ∧ a ∉ w.inputs ∧ a ∉ w.outputs := Iff.rfl

theorem internal_eq_diff (w : W P K) :
    w.internal = SDiff.sdiff (SDiff.sdiff w.buffers w.inputs) w.outputs := by
  ext a
  simp only [internal, Set.mem_ofPred_eq, Set.mem_sdiff, and_assoc]

/-- All produced IDs minted by (fresh slots of) node instances of the term. -/
def minted : W P K → Set K
  | .leaf l => l.minted
  | .series w₁ w₂ => w₁.minted ∪ w₂.minted
  | .par w₁ w₂ => w₁.minted ∪ w₂.minted

/-! Constructor-unfolding lemmas (definitional; stated for `simp`). -/

@[simp] theorem inputs_leaf (l : LeafInst P K) : (W.leaf l).inputs = l.inputs := rfl
@[simp] theorem inputs_series (w₁ w₂ : W P K) :
    (W.series w₁ w₂).inputs = w₁.inputs := rfl
@[simp] theorem inputs_par (w₁ w₂ : W P K) :
    (W.par w₁ w₂).inputs = w₁.inputs ∪ w₂.inputs := rfl

@[simp] theorem outputs_leaf (l : LeafInst P K) : (W.leaf l).outputs = l.outputs := rfl
@[simp] theorem outputs_series (w₁ w₂ : W P K) :
    (W.series w₁ w₂).outputs = w₂.outputs := rfl
@[simp] theorem outputs_par (w₁ w₂ : W P K) :
    (W.par w₁ w₂).outputs = w₁.outputs ∪ w₂.outputs := rfl

@[simp] theorem buffers_leaf (l : LeafInst P K) :
    (W.leaf l).buffers = l.inputs ∪ l.outputs := rfl
@[simp] theorem buffers_series (w₁ w₂ : W P K) :
    (W.series w₁ w₂).buffers = w₁.buffers ∪ w₂.buffers := rfl
@[simp] theorem buffers_par (w₁ w₂ : W P K) :
    (W.par w₁ w₂).buffers = w₁.buffers ∪ w₂.buffers := rfl

@[simp] theorem minted_leaf (l : LeafInst P K) : (W.leaf l).minted = l.minted := rfl
@[simp] theorem minted_series (w₁ w₂ : W P K) :
    (W.series w₁ w₂).minted = w₁.minted ∪ w₂.minted := rfl
@[simp] theorem minted_par (w₁ w₂ : W P K) :
    (W.par w₁ w₂).minted = w₁.minted ∪ w₂.minted := rfl

/-- The node instances of a term, in SP-tree left-to-right order.
Instance identity = position in this list (used from Stage 3 on). -/
def leaves : W P K → List (LeafInst P K)
  | .leaf l => [l]
  | .series w₁ w₂ => w₁.leaves ++ w₂.leaves
  | .par w₁ w₂ => w₁.leaves ++ w₂.leaves

@[simp] theorem leaves_leaf (l : LeafInst P K) : (W.leaf l).leaves = [l] := rfl
@[simp] theorem leaves_series (w₁ w₂ : W P K) :
    (W.series w₁ w₂).leaves = w₁.leaves ++ w₂.leaves := rfl
@[simp] theorem leaves_par (w₁ w₂ : W P K) :
    (W.par w₁ w₂).leaves = w₁.leaves ++ w₂.leaves := rfl

/-- A work term has at least one node instance (1.1: leaves are the base
case; there is no empty term). -/
theorem leaves_ne_nil (w : W P K) : w.leaves ≠ [] := by
  induction w with
  | leaf l => simp
  | series w₁ w₂ ih₁ ih₂ => simp [ih₁]
  | par w₁ w₂ ih₁ ih₂ => simp [ih₁]

/-! ### Stage-1 sanity theorems -/

theorem inputs_subset_buffers (w : W P K) : w.inputs ⊆ w.buffers := by
  induction w with
  | leaf l => exact Set.subset_union_left
  | series w₁ w₂ ih₁ ih₂ =>
      exact ih₁.trans Set.subset_union_left
  | par w₁ w₂ ih₁ ih₂ =>
      exact Set.union_subset_union ih₁ ih₂

theorem outputs_subset_buffers (w : W P K) : w.outputs ⊆ w.buffers := by
  induction w with
  | leaf l => exact Set.subset_union_right
  | series w₁ w₂ ih₁ ih₂ =>
      exact ih₂.trans Set.subset_union_right
  | par w₁ w₂ ih₁ ih₂ =>
      exact Set.union_subset_union ih₁ ih₂

theorem internal_subset_buffers (w : W P K) : w.internal ⊆ w.buffers :=
  fun _ h => h.1

theorem internal_disjoint_inputs (w : W P K) (a : Alloc P K) :
    a ∈ w.internal → a ∉ w.inputs := fun h => h.2.1

theorem internal_disjoint_outputs (w : W P K) (a : Alloc P K) :
    a ∈ w.internal → a ∉ w.outputs := fun h => h.2.2

/-- Minted IDs are the union of the per-instance minted sets. -/
theorem mem_minted_iff_leaves {w : W P K} {k : K} :
    k ∈ w.minted ↔ ∃ l ∈ w.leaves, k ∈ l.minted := by
  induction w with
  | leaf l => simp [minted]
  | series w₁ w₂ ih₁ ih₂ =>
      simp only [minted, Set.mem_union, ih₁, ih₂, leaves_series, List.mem_append]
      constructor
      · rintro (⟨l, hl, hk⟩ | ⟨l, hl, hk⟩) <;> exact ⟨l, by tauto, hk⟩
      · rintro ⟨l, hl | hl, hk⟩
        · exact Or.inl ⟨l, hl, hk⟩
        · exact Or.inr ⟨l, hl, hk⟩
  | par w₁ w₂ ih₁ ih₂ =>
      simp only [minted, Set.mem_union, ih₁, ih₂, leaves_par, List.mem_append]
      constructor
      · rintro (⟨l, hl, hk⟩ | ⟨l, hl, hk⟩) <;> exact ⟨l, by tauto, hk⟩
      · rintro ⟨l, hl | hl, hk⟩
        · exact Or.inl ⟨l, hl, hk⟩
        · exact Or.inr ⟨l, hl, hk⟩

/-- The buffers of a term are the union of the per-instance resolved slots. -/
theorem mem_buffers_iff_leaves {w : W P K} {a : Alloc P K} :
    a ∈ w.buffers ↔ ∃ l ∈ w.leaves, a ∈ l.inputs ∪ l.outputs := by
  induction w with
  | leaf l => simp [buffers]
  | series w₁ w₂ ih₁ ih₂ =>
      simp only [buffers, Set.mem_union, ih₁, ih₂, leaves_series, List.mem_append]
      constructor
      · rintro (⟨l, hl, hk⟩ | ⟨l, hl, hk⟩) <;> exact ⟨l, by tauto, hk⟩
      · rintro ⟨l, hl | hl, hk⟩
        · exact Or.inl ⟨l, hl, hk⟩
        · exact Or.inr ⟨l, hl, hk⟩
  | par w₁ w₂ ih₁ ih₂ =>
      simp only [buffers, Set.mem_union, ih₁, ih₂, leaves_par, List.mem_append]
      constructor
      · rintro (⟨l, hl, hk⟩ | ⟨l, hl, hk⟩) <;> exact ⟨l, by tauto, hk⟩
      · rintro ⟨l, hl | hl, hk⟩
        · exact Or.inl ⟨l, hl, hk⟩
        · exact Or.inr ⟨l, hl, hk⟩

end W

/-! ## §3.3 Validation

Lengths: a parameter carries a declared `(len, align)` (2.1), given by an
ambient declaration context; a produced ID carries the `len` declared at the
fresh slot that mints it.  Since minting is a per-instance local fact, the
produced-ID length is *relational* here; `WF` (Stage 2) makes the minting
slot unique, so the relation is functional on well-formed terms. -/

/-- Declaration context for parameters (2.1): each `p ∈ 𝔸_π` has a fixed
declared length and alignment (stored as log₂). -/
structure ParamDecl (P : Type*) where
  len : P → ℕ
  alignLog : P → ℕ

/-- `MintSpec w k len alog`: some node instance of `w` mints `k` at a fresh
output slot declared with length `len` and alignment `2^alog`. -/
def W.MintSpec {P K : Type*} (w : W P K) (k : K) (len alog : ℕ) : Prop :=
  ∃ l ∈ w.leaves, ∃ i, l.sig.prov i = none ∧ l.mint i = k ∧
    l.sig.freshLen i = len ∧ l.sig.freshAlignLog i = alog

/-- Declared length of an allocation ID, relative to the term (relational for
produced IDs; see `MintSpec`). -/
def W.AllocLen {P K : Type*} (pd : ParamDecl P) (w : W P K) :
    Alloc P K → ℕ → Prop
  | .param p, n => pd.len p = n
  | .prod k, n => ∃ alog, w.MintSpec k n alog

/-- **§3.3 (Validation).**  Per input slot, after resolution, the slot's
declared `len` equals the length of the resolved allocation.  Per-slot
checks only — no constraint solving. -/
def W.LenValid {P K : Type*} (pd : ParamDecl P) (w : W P K) : Prop :=
  ∀ l ∈ w.leaves, ∀ j : Fin l.sig.nIn, w.AllocLen pd (l.bind j) (l.sig.inLen j)

end WorkGraph
