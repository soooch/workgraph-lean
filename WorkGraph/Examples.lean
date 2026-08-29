/-
# Work Graph Model — Stage 5: A concrete worked example

A two-node copy chain `Series(Leaf(A), Leaf(B), θ)` with
`A : x ↦ fresh t₀` and `B : t₀ ↦ fresh t₁`, θ binding B's input to A's
output.  Demonstrates that every layer of the formalization is inhabited and
computes as the spec says:

* the term is well-formed (`wf_chain`) and length-valid (`lenValid_chain`);
* its interface and internal sets are as expected: input `x`, output `t₁`,
  internal `t₀` (the D5 unfolding in the smallest nontrivial case);
* it has a well-formed schedule with A ≺ B (`prec_chain`, and again via the
  generic D9 theorem in `prec_chain'`);
* D10 concretely: A's fresh output conflicts with A's input
  (`mayOverlap_chain`) — the ping-pong obligation — and D12 concretely: the
  input is pinned against the output (`mayOverlap_interface_chain`).

Parameters are named by strings, produced IDs by naturals.  (`abbrev` keeps
the slot types reducible so that `Fin` literals elaborate.)
-/
import WorkGraph.Reuse

namespace WorkGraph.Examples

open WorkGraph

/-- A 16-byte, 4-aligned copy-shaped node: one input slot, one fresh output
slot. -/
abbrev copySig : NodeSig where
  nIn := 1
  nOut := 1
  prov := fun _ => none
  inLen := fun _ => 16
  inAlignLog := fun _ => 2
  freshLen := fun _ => 16
  freshAlignLog := fun _ => 2

/-- Node A: reads parameter `x`, mints produced ID `0`. -/
abbrev leafA : LeafInst String ℕ where
  sig := copySig
  bind := fun _ => .param "x"
  mint := fun _ => 0

/-- Node B (standalone): reads parameter `y`, mints produced ID `1`. -/
abbrev leafB : LeafInst String ℕ where
  sig := copySig
  bind := fun _ => .param "y"
  mint := fun _ => 1

/-- θ: route A's output (produced ID 0) into B's input `y`. -/
def θAB : Subst String ℕ := fun a =>
  if a = .param "y" then some (.prod 0) else none

/-- The chain `Series(Leaf(A), Leaf(B), θAB)`. -/
def chain : W String ℕ := (W.leaf leafA).mkSeries (W.leaf leafB) θAB

/-- `Fin 1` has one element (used for the one-slot signatures). -/
private theorem finOne (i i' : Fin 1) : i = i' := Fin.ext (by omega)

theorem wf_leafA : WF (W.leaf leafA) :=
  WF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i')

theorem wf_leafB : WF (W.leaf leafB) :=
  WF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i')

theorem thetaFits_AB : ThetaFits θAB (W.leaf leafA) (W.leaf leafB) where
  dom_eq := by
    intro a
    constructor
    · intro hsome
      by_cases h : a = Alloc.param "y"
      · subst h
        exact ⟨0, rfl⟩
      · simp [θAB, if_neg h] at hsome
    · rintro ⟨j, rfl⟩
      simp [θAB]
  codom := by
    intro a b h
    simp only [θAB] at h
    split at h
    · cases h
      exact ⟨0, rfl⟩
    · cases h

theorem mintDisjoint_AB : MintDisjoint (W.leaf leafA) (W.leaf leafB) := by
  rintro k ⟨i, -, rfl⟩ ⟨i', -, hk⟩
  simp at hk

theorem wf_chain : WF chain :=
  WF.series wf_leafA wf_leafB thetaFits_AB mintDisjoint_AB

/-! ### §3.3 validation on the chain -/

def pd : ParamDecl String where
  len := fun _ => 16
  alignLog := fun _ => 2

theorem lenValid_chain : chain.LenValid pd := by
  intro l hl j
  simp only [chain, W.mkSeries, W.rebind, W.leaves_series, W.leaves_leaf,
    List.mem_append, List.mem_singleton] at hl
  rcases hl with rfl | rfl
  · -- A's input is the parameter x, declared with length 16
    rfl
  · -- B's input was rewritten to A's fresh output, minted with length 16
    show chain.AllocLen pd (.prod 0) 16
    exact ⟨2, leafA, List.Mem.head _, 0, rfl, rfl, rfl, rfl⟩

/-! ### Interface and internal sets: input x, output t₁, internal t₀ -/

example : Alloc.param "x" ∈ chain.inputs := ⟨0, rfl⟩

example : Alloc.prod 1 ∈ chain.outputs := ⟨(0 : Fin 1), rfl⟩

/-- D5 in the smallest nontrivial case: the intermediate buffer is internal. -/
theorem internal_chain : Alloc.prod 0 ∈ chain.internal := by
  refine ⟨Or.inr (Or.inl ⟨(0 : Fin 1), rfl⟩), ?_, ?_⟩
  · rintro ⟨j, hj⟩
    simp at hj
  · rintro ⟨kk, hk⟩
    simp [LeafInst.resOut, LeafInst.rebind] at hk

/-! ### A schedule with A ≺ B, and D10 concretely -/

/-- The (unique) schedule of the chain. -/
def sChain : SW String ℕ :=
  SW.series (SW.leaf leafA) ((SW.leaf leafB).rebind θAB)

theorem swf_chain : SWF sChain :=
  SWF.series (SWF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i'))
    (SWF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i'))
    thetaFits_AB mintDisjoint_AB

theorem sChain_forget : sChain.forget = chain := rfl

/-- A ≺ B: the Series clause of 4.3. -/
theorem prec_chain : sChain.Prec (.inst 0) (.inst 1) := by
  have h := SW.SGen.seriesCross (s₁ := SW.leaf leafA)
    (s₂ := (SW.leaf leafB).rebind θAB) (i := 0) (j := 0) (by simp) (by simp)
  have e : (SW.leaf leafA).nLeaves + 0 = 1 := by simp
  rw [e] at h
  exact Relation.TransGen.single (SW.Gen.struct h)

/-- D9 concretely: B's input resolves to `t₀`, produced at A, and the
generic theorem derives A ≺ B. -/
theorem prec_chain' : sChain.Prec (.inst 0) (.inst 1) := by
  refine swf_chain.producer_prec_consumer (a := .prod 0) ?_ ?_
  · exact ⟨leafB.rebind θAB, rfl,
      ⟨(0 : Fin 1), by simp [LeafInst.rebind, Subst.apply, θAB]⟩⟩
  · exact ⟨0, rfl, leafA, rfl, ⟨0, rfl, rfl⟩⟩

/-- **D10 concretely**: A's fresh output `t₀` conflicts with A's input `x` —
under any valid assignment they get disjoint intervals (ping-pong). -/
theorem mayOverlap_chain : MayOverlap sChain (.param "x") (.prod 0) :=
  swf_chain.mayOverlap_fresh_input (i := 0) (l := leafA) rfl 0 (k := 0) rfl

/-- D12 concretely: the chain's input is pinned against its output. -/
theorem mayOverlap_interface_chain : MayOverlap sChain (.param "x") (.prod 1) :=
  swf_chain.mayOverlap_input ⟨0, rfl⟩ (Or.inr (Or.inr ⟨(0 : Fin 1), rfl⟩))

/-! ### Instance identity is by instantiation (1.1/2.4)

Formation operands never share node instances: "a term is consumed by the
formation that uses it, and reusing one requires re-instantiation" (2.4).
In this formalization that discipline surfaces as the mint-distinctness
side condition of well-formedness (2.1). -/

/-- **Duplicate-leaf rejection**: putting the *same* leaf instance on both
sides of a Par is not well-formed, in any mode — both arms would mint the
same produced ID, violating global distinctness (2.1). -/
theorem not_swf_duplicate_leaf (m : Mode) :
    ¬ SWF (SW.par m (SW.leaf leafA) (SW.leaf leafA)) := by
  intro h
  cases h with
  | par _ _ hd => exact hd 0 ⟨0, rfl, rfl⟩ ⟨0, rfl, rfl⟩

/-- The positive companion: two *distinct instantiations* — here of the same
primitive signature `copySig`, with distinct minted IDs and distinct
bindings — compose fine in Par, in any mode.  Instance identity is by
instantiation, never by primitive symbol (1.1). -/
theorem swf_two_instances (m : Mode) :
    SWF (SW.par m (SW.leaf leafA) (SW.leaf leafB)) :=
  SWF.par (SWF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i'))
    (SWF.leaf (fun _ => trivial) (fun i i' _ _ _ => finOne i i'))
    mintDisjoint_AB

end WorkGraph.Examples
