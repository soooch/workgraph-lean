/-
# Work Graph Model — Stage 3: Schedules, precedence, D7/D8/D9

Formalizes §4.3 (schedule and order) together with the node-instance side of
§4.2 (sentinels σ/τ as `PNode.src`/`PNode.sink`), and proves:

* **D8**: ≺ is a strict partial order (`prec_irrefl`, `prec_asymm`,
  transitivity by construction) — proved exactly as the spec argues, by
  embedding the generators into the left-to-right linearization of the SP
  tree taken with mode order (`linRank`, with σ prepended and τ appended in
  `nodeRank`).

* **D7** (no in-place / unique writer): a produced ID has at most one minting
  instance (`SWF.mintsAt_unique`) — with `WF.mem_minted_of_prod_mem_buffers`
  (D4), every allocation occurring in the finalized graph has exactly one
  true producer (`exists_producer` + uniqueness; σ produces the parameters,
  4.2).

* **D9** (dataflow respects ≺): for every allocation `a` and every consumer
  `c ≠ producer(a)`, `producer(a) ≺ c` (`SWF.producer_prec_consumer` for
  instance consumers, `producer_prec_sink` for the sentinel sink τ).

Node instances are identified by their index in the SP-tree's left-to-right
leaf enumeration (`SW.leaves`); σ and τ are the extra `PNode`s of 4.2.
-/
import WorkGraph.Composition
import Mathlib.Logic.Relation

namespace WorkGraph

variable {P K : Type*}

/-! ## Indexed-list membership helper -/

/-- `AtIdx L i Q`: position `i` of `L` holds an element satisfying `Q`. -/
def AtIdx {α : Type*} (L : List α) (i : ℕ) (Q : α → Prop) : Prop :=
  ∃ l, L[i]? = some l ∧ Q l

theorem AtIdx.lt_length {α : Type*} {L : List α} {i : ℕ} {Q : α → Prop}
    (h : AtIdx L i Q) : i < L.length := by
  obtain ⟨l, hl, -⟩ := h
  obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hl
  exact h

theorem atIdx_append {α : Type*} {L₁ L₂ : List α} {i : ℕ} {Q : α → Prop} :
    AtIdx (L₁ ++ L₂) i Q ↔
      (i < L₁.length ∧ AtIdx L₁ i Q) ∨
      (L₁.length ≤ i ∧ AtIdx L₂ (i - L₁.length) Q) := by
  constructor
  · rintro ⟨l, hl, hQ⟩
    by_cases h : i < L₁.length
    · rw [List.getElem?_append_left h] at hl
      exact Or.inl ⟨h, l, hl, hQ⟩
    · rw [List.getElem?_append_right (by omega)] at hl
      exact Or.inr ⟨by omega, l, hl, hQ⟩
  · rintro (⟨h, l, hl, hQ⟩ | ⟨h, l, hl, hQ⟩)
    · exact ⟨l, by rw [List.getElem?_append_left h]; exact hl, hQ⟩
    · exact ⟨l, by rw [List.getElem?_append_right h]; exact hl, hQ⟩

theorem atIdx_map {α β : Type*} {L : List α} {f : α → β} {i : ℕ} {Q : β → Prop} :
    AtIdx (L.map f) i Q ↔ AtIdx L i (fun l => Q (f l)) := by
  constructor
  · rintro ⟨l, hl, hQ⟩
    rw [List.getElem?_map] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨l₀, hl₀, hQ⟩
  · rintro ⟨l, hl, hQ⟩
    exact ⟨f l, by rw [List.getElem?_map, hl]; rfl, hQ⟩

/-! ## §4.3 Schedules -/

/-- A Par mode (4.3). -/
inductive Mode where
  | conc | seq12 | seq21
deriving DecidableEq

/-- A *scheduled* work term: the SP tree with a mode assigned to every Par
node.  A schedule S for `w` is an `s : SW` with `s.forget = w`. -/
inductive SW (P K : Type*) where
  | leaf (l : LeafInst P K)
  | series (s₁ s₂ : SW P K)
  | par (m : Mode) (s₁ s₂ : SW P K)

namespace SW

/-- Erase the schedule annotations. -/
def forget : SW P K → W P K
  | .leaf l => .leaf l
  | .series s₁ s₂ => .series s₁.forget s₂.forget
  | .par _ s₁ s₂ => .par s₁.forget s₂.forget

@[simp] theorem forget_leaf (l : LeafInst P K) : (SW.leaf l).forget = .leaf l := rfl
@[simp] theorem forget_series (s₁ s₂ : SW P K) :
    (SW.series s₁ s₂).forget = .series s₁.forget s₂.forget := rfl
@[simp] theorem forget_par (m : Mode) (s₁ s₂ : SW P K) :
    (SW.par m s₁ s₂).forget = .par s₁.forget s₂.forget := rfl

/-- Node instances in SP-tree left-to-right order (instance = index). -/
def leaves : SW P K → List (LeafInst P K)
  | .leaf l => [l]
  | .series s₁ s₂ => s₁.leaves ++ s₂.leaves
  | .par _ s₁ s₂ => s₁.leaves ++ s₂.leaves

@[simp] theorem leaves_leaf (l : LeafInst P K) : (SW.leaf l).leaves = [l] := rfl
@[simp] theorem leaves_series (s₁ s₂ : SW P K) :
    (SW.series s₁ s₂).leaves = s₁.leaves ++ s₂.leaves := rfl
@[simp] theorem leaves_par (m : Mode) (s₁ s₂ : SW P K) :
    (SW.par m s₁ s₂).leaves = s₁.leaves ++ s₂.leaves := rfl

@[simp] theorem leaves_forget (s : SW P K) : s.forget.leaves = s.leaves := by
  induction s with
  | leaf l => rfl
  | series s₁ s₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | par m s₁ s₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Number of node instances. -/
def nLeaves (s : SW P K) : ℕ := s.leaves.length

@[simp] theorem nLeaves_leaf (l : LeafInst P K) : (SW.leaf l).nLeaves = 1 := rfl
@[simp] theorem nLeaves_series (s₁ s₂ : SW P K) :
    (SW.series s₁ s₂).nLeaves = s₁.nLeaves + s₂.nLeaves := by
  simp [nLeaves]
@[simp] theorem nLeaves_par (m : Mode) (s₁ s₂ : SW P K) :
    (SW.par m s₁ s₂).nLeaves = s₁.nLeaves + s₂.nLeaves := by
  simp [nLeaves]

theorem nLeaves_pos (s : SW P K) : 0 < s.nLeaves := by
  induction s with
  | leaf l => simp
  | series s₁ s₂ ih₁ ih₂ => rw [nLeaves_series]; omega
  | par m s₁ s₂ ih₁ ih₂ => rw [nLeaves_par]; omega

/-- Rebind a scheduled term (the scheduled analogue of `W.rebind`). -/
def rebind (s : SW P K) (θ : Subst P K) : SW P K :=
  match s with
  | .leaf l => .leaf (l.rebind θ)
  | .series s₁ s₂ => .series (s₁.rebind θ) (s₂.rebind θ)
  | .par m s₁ s₂ => .par m (s₁.rebind θ) (s₂.rebind θ)

@[simp] theorem forget_rebind (s : SW P K) (θ : Subst P K) :
    (s.rebind θ).forget = s.forget.rebind θ := by
  induction s with
  | leaf l => rfl
  | series s₁ s₂ ih₁ ih₂ => simp [rebind, W.rebind, ih₁, ih₂]
  | par m s₁ s₂ ih₁ ih₂ => simp [rebind, W.rebind, ih₁, ih₂]

@[simp] theorem leaves_rebind (s : SW P K) (θ : Subst P K) :
    (s.rebind θ).leaves = s.leaves.map (·.rebind θ) := by
  induction s with
  | leaf l => rfl
  | series s₁ s₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]
  | par m s₁ s₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]

@[simp] theorem nLeaves_rebind (s : SW P K) (θ : Subst P K) :
    (s.rebind θ).nLeaves = s.nLeaves := by
  simp [nLeaves]

end SW

/-- Well-formed *scheduled* terms: a schedule of a term built by the legal
formations (mirror of `WF` on the annotated tree; modes are unconstrained —
"a schedule S assigns each Par node a mode", 4.3). -/
inductive SWF : SW P K → Prop
  | leaf {l : LeafInst P K} :
      (∀ j, (l.bind j).IsParam) → l.MintInj → SWF (.leaf l)
  | series {s₁ s₂ : SW P K} {θ : Subst P K} :
      SWF s₁ → SWF s₂ → ThetaFits θ s₁.forget s₂.forget →
      MintDisjoint s₁.forget s₂.forget → SWF (.series s₁ (s₂.rebind θ))
  | par {m : Mode} {s₁ s₂ : SW P K} :
      SWF s₁ → SWF s₂ → MintDisjoint s₁.forget s₂.forget →
      SWF (.par m s₁ s₂)

/-- Inversion for `SWF` at a Series node: the right arm is a rewritten
well-formed schedule under a fitting substitution.  (Lets a holder of a
composite `SWF` apply the arm-hypothesis theorems below.) -/
theorem SWF.series_elim {s₁ s₂' : SW P K} (h : SWF (.series s₁ s₂')) :
    SWF s₁ ∧ ∃ (s₂ : SW P K) (θ : Subst P K), s₂' = s₂.rebind θ ∧ SWF s₂ ∧
      ThetaFits θ s₁.forget s₂.forget ∧ MintDisjoint s₁.forget s₂.forget := by
  cases h with
  | series h₁ h₂ hθ hd => exact ⟨h₁, _, _, rfl, h₂, hθ, hd⟩

/-- Inversion for `SWF` at a Par node. -/
theorem SWF.par_elim {m : Mode} {s₁ s₂ : SW P K} (h : SWF (.par m s₁ s₂)) :
    SWF s₁ ∧ SWF s₂ ∧ MintDisjoint s₁.forget s₂.forget := by
  cases h with
  | par h₁ h₂ hd => exact ⟨h₁, h₂, hd⟩

/-- A well-formed schedule schedules a well-formed term. -/
theorem SWF.forget_wf {s : SW P K} (h : SWF s) : WF s.forget := by
  induction h with
  | leaf hβ hm => exact WF.leaf hβ hm
  | @series s₁ s₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      have he : (SW.series s₁ (s₂.rebind θ)).forget = s₁.forget.mkSeries s₂.forget θ := by
        simp [W.mkSeries]
      rw [he]
      exact WF.series ih₁ ih₂ hθ hd
  | par h₁ h₂ hd ih₁ ih₂ => exact WF.par ih₁ ih₂ hd

/-- Conversely, every well-formed term admits a schedule (e.g. all-concurrent):
scheduling is total, chosen freely at finalization (4.1/4.3). -/
theorem WF.exists_schedule {w : W P K} (h : WF w) :
    ∃ s : SW P K, s.forget = w ∧ SWF s := by
  induction h with
  | @leaf l hβ hm => exact ⟨.leaf l, rfl, .leaf hβ hm⟩
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      obtain ⟨s₁, rfl, hs₁⟩ := ih₁
      obtain ⟨s₂, rfl, hs₂⟩ := ih₂
      exact ⟨.series s₁ (s₂.rebind θ), by simp [W.mkSeries], .series hs₁ hs₂ hθ hd⟩
  | @par w₁ w₂ h₁ h₂ hd ih₁ ih₂ =>
      obtain ⟨s₁, rfl, hs₁⟩ := ih₁
      obtain ⟨s₂, rfl, hs₂⟩ := ih₂
      exact ⟨.par .conc s₁ s₂, rfl, .par hs₁ hs₂ hd⟩

/-- Rebinding is surjective on schedules of the right shape: a schedule
whose erasure is a rewritten term is itself a rewritten schedule (modes are
untouched by rebinding). -/
theorem SW.exists_rebind_preimage {θ : Subst P K} :
    ∀ {s : SW P K} {w : W P K}, s.forget = w.rebind θ →
      ∃ t : SW P K, t.forget = w ∧ t.rebind θ = s := by
  intro s
  induction s with
  | leaf l =>
      intro w h
      cases w with
      | leaf l₀ =>
          simp only [SW.forget, W.rebind] at h
          injection h with h'
          exact ⟨.leaf l₀, rfl, by rw [SW.rebind, h']⟩
      | series w₁ w₂ => simp [W.rebind, SW.forget] at h
      | par w₁ w₂ => simp [W.rebind, SW.forget] at h
  | series s₁ s₂ ih₁ ih₂ =>
      intro w h
      cases w with
      | leaf l₀ => simp [W.rebind, SW.forget] at h
      | series w₁ w₂ =>
          simp only [SW.forget_series, W.rebind] at h
          injection h with h₁ h₂
          obtain ⟨t₁, ht₁, ht₁'⟩ := ih₁ h₁
          obtain ⟨t₂, ht₂, ht₂'⟩ := ih₂ h₂
          exact ⟨.series t₁ t₂, by simp [ht₁, ht₂],
            by rw [SW.rebind, ht₁', ht₂']⟩
      | par w₁ w₂ => simp [W.rebind, SW.forget] at h
  | par m s₁ s₂ ih₁ ih₂ =>
      intro w h
      cases w with
      | leaf l₀ => simp [W.rebind, SW.forget] at h
      | series w₁ w₂ => simp [W.rebind, SW.forget] at h
      | par w₁ w₂ =>
          simp only [SW.forget_par, W.rebind] at h
          injection h with h₁ h₂
          obtain ⟨t₁, ht₁, ht₁'⟩ := ih₁ h₁
          obtain ⟨t₂, ht₂, ht₂'⟩ := ih₂ h₂
          exact ⟨.par m t₁ t₂, by simp [ht₁, ht₂],
            by rw [SW.rebind, ht₁', ht₂']⟩

/-- **4.3, ∀-form**: *every* mode assignment of a well-formed term is a
well-formed schedule — "a schedule S assigns each Par node in W a mode",
with no further condition.  (Shape-paired induction with `WF` inversion;
the Series case pulls the schedule of the rewritten arm back through
`SW.exists_rebind_preimage`.) -/
theorem WF.swf_of_forget {w : W P K} (h : WF w) :
    ∀ s : SW P K, s.forget = w → SWF s := by
  induction h with
  | @leaf l hβ hm =>
      intro s hs
      cases s with
      | leaf l' =>
          injection hs with h'
          subst h'
          exact SWF.leaf hβ hm
      | series s₁ s₂ => simp at hs
      | par m s₁ s₂ => simp at hs
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro s hs
      cases s with
      | leaf l' => simp [W.mkSeries] at hs
      | par m s₁ s₂ => simp [W.mkSeries] at hs
      | series s₁ s₂ =>
          simp only [SW.forget_series, W.mkSeries] at hs
          injection hs with hs₁ hs₂
          obtain ⟨t₂, ht₂, rfl⟩ := SW.exists_rebind_preimage hs₂
          exact SWF.series (ih₁ s₁ hs₁) (ih₂ t₂ ht₂)
            (by rw [hs₁, ht₂]; exact hθ) (by rw [hs₁, ht₂]; exact hd)
  | @par w₁ w₂ h₁ h₂ hd ih₁ ih₂ =>
      intro s hs
      cases s with
      | leaf l' => simp at hs
      | series s₁ s₂ => simp at hs
      | par m s₁ s₂ =>
          simp only [SW.forget_par] at hs
          injection hs with hs₁ hs₂
          exact SWF.par (ih₁ s₁ hs₁) (ih₂ s₂ hs₂)
            (by rw [hs₁, hs₂]; exact hd)

/-! ## §4.2/§4.3 Nodes of the finalized graph and the generators of ≺ -/

/-- A node of the finalized graph: the sentinel source σ, a node instance
(by leaf index), or the sentinel sink τ (4.2). -/
inductive PNode where
  | src
  | inst (i : ℕ)
  | sink
deriving DecidableEq

/-- Index relabeling when a subterm embeds as a right arm. -/
def PNode.shift (n : ℕ) : PNode → PNode
  | .src => .src
  | .inst i => .inst (n + i)
  | .sink => .sink

namespace SW

/-- Structural generator pairs of ≺ (4.3), between instance indices:
`Series(W₁, W₂)` orders all of W₁ before all of W₂; a `seq(i,j)` Par orders
all of Wᵢ before all of Wⱼ; a concurrent Par generates nothing. -/
inductive SGen : SW P K → ℕ → ℕ → Prop
  | seriesCross {s₁ s₂ : SW P K} {i j : ℕ} :
      i < s₁.nLeaves → j < s₂.nLeaves →
      SGen (.series s₁ s₂) i (s₁.nLeaves + j)
  | seriesLeft {s₁ s₂ : SW P K} {i j : ℕ} :
      SGen s₁ i j → SGen (.series s₁ s₂) i j
  | seriesRight {s₁ s₂ : SW P K} {i j : ℕ} :
      SGen s₂ i j → SGen (.series s₁ s₂) (s₁.nLeaves + i) (s₁.nLeaves + j)
  | parCross12 {s₁ s₂ : SW P K} {i j : ℕ} :
      i < s₁.nLeaves → j < s₂.nLeaves →
      SGen (.par .seq12 s₁ s₂) i (s₁.nLeaves + j)
  | parCross21 {s₁ s₂ : SW P K} {i j : ℕ} :
      i < s₂.nLeaves → j < s₁.nLeaves →
      SGen (.par .seq21 s₁ s₂) (s₁.nLeaves + i) j
  | parLeft {m : Mode} {s₁ s₂ : SW P K} {i j : ℕ} :
      SGen s₁ i j → SGen (.par m s₁ s₂) i j
  | parRight {m : Mode} {s₁ s₂ : SW P K} {i j : ℕ} :
      SGen s₂ i j → SGen (.par m s₁ s₂) (s₁.nLeaves + i) (s₁.nLeaves + j)

theorem SGen.bounds {s : SW P K} {i j : ℕ} (h : SGen s i j) :
    i < s.nLeaves ∧ j < s.nLeaves := by
  induction h with
  | @seriesCross s₁ s₂ i j h₁ h₂ => rw [nLeaves_series]; omega
  | @seriesLeft s₁ s₂ i j h ih => rw [nLeaves_series]; omega
  | @seriesRight s₁ s₂ i j h ih => rw [nLeaves_series]; omega
  | @parCross12 s₁ s₂ i j h₁ h₂ => rw [nLeaves_par]; omega
  | @parCross21 s₁ s₂ i j h₁ h₂ => rw [nLeaves_par]; omega
  | @parLeft m s₁ s₂ i j h ih => rw [nLeaves_par]; omega
  | @parRight m s₁ s₂ i j h ih => rw [nLeaves_par]; omega

/-- Full generator set of ≺ (4.3): the structural pairs plus the endpoint
pairs `(σ, n)` and `(n, τ)` for every node instance `n`. -/
inductive Gen (s : SW P K) : PNode → PNode → Prop
  | struct {i j : ℕ} : SGen s i j → Gen s (.inst i) (.inst j)
  | fromSrc {i : ℕ} : i < s.nLeaves → Gen s .src (.inst i)
  | toSink {i : ℕ} : i < s.nLeaves → Gen s (.inst i) .sink

/-- **≺** (4.3): the transitive closure of the generators. -/
abbrev Prec (s : SW P K) : PNode → PNode → Prop := Relation.TransGen (Gen s)

/-! ### D8: ≺ embeds in the mode-ordered linearization -/

/-- Rank in an appended pair of blocks: the left block (ranked by `r₁`)
precedes the right block (ranked by `r₂`, shifted past `n₁`).  Shared by
the Series, concurrent-Par, and `seq(1,2)`-Par arms of `linRank`; only
`seq(2,1)`'s reversed construction stays separate. -/
def appendRank (n₁ : ℕ) (r₁ r₂ : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n₁ then r₁ i else n₁ + r₂ (i - n₁)

theorem appendRank_lt {n₁ n₂ : ℕ} {r₁ r₂ : ℕ → ℕ}
    (h₁ : ∀ i, r₁ i < n₁) (h₂ : ∀ i, r₂ i < n₂) (i : ℕ) :
    appendRank n₁ r₁ r₂ i < n₁ + n₂ := by
  unfold appendRank
  split
  · have := h₁ i; omega
  · have := h₂ (i - n₁); omega

theorem appendRank_left {n₁ : ℕ} {r₁ r₂ : ℕ → ℕ} {i : ℕ} (hi : i < n₁) :
    appendRank n₁ r₁ r₂ i = r₁ i := if_pos hi

theorem appendRank_right {n₁ : ℕ} {r₁ r₂ : ℕ → ℕ} {i : ℕ} :
    appendRank n₁ r₁ r₂ (n₁ + i) = n₁ + r₂ i := by
  unfold appendRank
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem appendRank_cross {n₁ : ℕ} {r₁ r₂ : ℕ → ℕ} {i j : ℕ}
    (h₁ : ∀ i, r₁ i < n₁) (hi : i < n₁) :
    appendRank n₁ r₁ r₂ i < appendRank n₁ r₁ r₂ (n₁ + j) := by
  rw [appendRank_left hi, appendRank_right]
  have := h₁ i
  omega

/-- Position of instance `i` in the left-to-right linearization of the SP
tree *taken with mode order*: `seq(2,1)` reverses its branches (D8).
(A concurrent Par is linearized arbitrarily left-then-right; its generators
are empty, so any consistent placement works.)  Total in `i` for
convenience; only values at `i < nLeaves` are meaningful. -/
def linRank : SW P K → ℕ → ℕ
  | .leaf _, _ => 0
  | .series s₁ s₂, i => appendRank s₁.nLeaves s₁.linRank s₂.linRank i
  | .par .seq21 s₁ s₂, i =>
      if i < s₁.nLeaves then s₂.nLeaves + s₁.linRank i
      else s₂.linRank (i - s₁.nLeaves)
  | .par .conc s₁ s₂, i => appendRank s₁.nLeaves s₁.linRank s₂.linRank i
  | .par .seq12 s₁ s₂, i => appendRank s₁.nLeaves s₁.linRank s₂.linRank i

theorem linRank_lt (s : SW P K) (i : ℕ) : s.linRank i < s.nLeaves := by
  induction s generalizing i with
  | leaf l => simp [linRank]
  | series s₁ s₂ ih₁ ih₂ =>
      rw [nLeaves_series]
      simp only [linRank]
      exact appendRank_lt ih₁ ih₂ i
  | par m s₁ s₂ ih₁ ih₂ =>
      rw [nLeaves_par]
      cases m with
      | conc =>
          simp only [linRank]
          exact appendRank_lt ih₁ ih₂ i
      | seq12 =>
          simp only [linRank]
          exact appendRank_lt ih₁ ih₂ i
      | seq21 =>
          simp only [linRank]
          split
          · have := ih₁ i; omega
          · have := ih₂ (i - s₁.nLeaves); omega

/-- Every structural generator pair respects the linearization (D8). -/
theorem SGen.linRank_lt_linRank {s : SW P K} {i j : ℕ} (h : SGen s i j) :
    s.linRank i < s.linRank j := by
  induction h with
  | @seriesCross s₁ s₂ i j h₁ h₂ =>
      simp only [linRank]
      exact appendRank_cross (linRank_lt s₁) h₁
  | @seriesLeft s₁ s₂ i j h ih =>
      obtain ⟨hi, hj⟩ := h.bounds
      simp only [linRank]
      rw [appendRank_left hi, appendRank_left hj]
      exact ih
  | @seriesRight s₁ s₂ i j h ih =>
      simp only [linRank]
      rw [appendRank_right, appendRank_right]
      omega
  | @parCross12 s₁ s₂ i j h₁ h₂ =>
      simp only [linRank]
      exact appendRank_cross (linRank_lt s₁) h₁
  | @parCross21 s₁ s₂ i j h₁ h₂ =>
      simp only [linRank]
      rw [if_neg (by omega), if_pos h₂]
      have hr := linRank_lt s₂ i
      have he : s₁.nLeaves + i - s₁.nLeaves = i := by omega
      rw [he]
      omega
  | @parLeft m s₁ s₂ i j h ih =>
      obtain ⟨hi, hj⟩ := h.bounds
      cases m with
      | conc =>
          simp only [linRank]
          rw [appendRank_left hi, appendRank_left hj]
          exact ih
      | seq12 =>
          simp only [linRank]
          rw [appendRank_left hi, appendRank_left hj]
          exact ih
      | seq21 =>
          simp only [linRank]
          rw [if_pos hi, if_pos hj]
          omega
  | @parRight m s₁ s₂ i j h ih =>
      cases m with
      | conc =>
          simp only [linRank]
          rw [appendRank_right, appendRank_right]
          omega
      | seq12 =>
          simp only [linRank]
          rw [appendRank_right, appendRank_right]
          omega
      | seq21 =>
          simp only [linRank]
          rw [if_neg (by omega), if_neg (by omega)]
          have e₁ : s₁.nLeaves + i - s₁.nLeaves = i := by omega
          have e₂ : s₁.nLeaves + j - s₁.nLeaves = j := by omega
          rw [e₁, e₂]
          omega

/-- Rank in the full linearization: σ first, instances by `linRank`, τ last
(D8: "with σ prepended and τ appended"). -/
def nodeRank (s : SW P K) : PNode → ℕ
  | .src => 0
  | .inst i => s.linRank i + 1
  | .sink => s.nLeaves + 1

theorem nodeRank_le (s : SW P K) (a : PNode) : s.nodeRank a ≤ s.nLeaves + 1 := by
  cases a with
  | src => simp [nodeRank]
  | inst i => have := linRank_lt s i; simp only [nodeRank]; omega
  | sink => simp [nodeRank]

/-- Every generator pair increases the linearization rank (D8: "the
generators embed in a total order"). -/
theorem Gen.nodeRank_lt {s : SW P K} {a b : PNode} (h : Gen s a b) :
    s.nodeRank a < s.nodeRank b := by
  cases h with
  | struct hs => have := hs.linRank_lt_linRank; simp only [nodeRank]; omega
  | fromSrc hi => simp only [nodeRank]; omega
  | @toSink i hi => have := linRank_lt s i; simp only [nodeRank]; omega

theorem Prec.nodeRank_lt {s : SW P K} {a b : PNode} (h : s.Prec a b) :
    s.nodeRank a < s.nodeRank b := by
  induction h with
  | single h => exact h.nodeRank_lt
  | tail _ h ih => exact ih.trans h.nodeRank_lt

/-- **D8**: ≺ is irreflexive (and transitive by construction) — a strict
partial order. -/
theorem prec_irrefl (s : SW P K) (a : PNode) : ¬ s.Prec a a :=
  fun h => lt_irrefl _ h.nodeRank_lt

theorem prec_asymm {s : SW P K} {a b : PNode} (h : s.Prec a b)
    (h' : s.Prec b a) : False :=
  lt_asymm h.nodeRank_lt h'.nodeRank_lt

/-- Nothing precedes σ (4.2/D12: inputs are pinned from the start). -/
theorem not_prec_src {s : SW P K} {a : PNode} : ¬ s.Prec a .src := by
  intro h
  have h₁ := h.nodeRank_lt
  rw [show s.nodeRank .src = 0 from rfl] at h₁
  omega

/-- Nothing satisfies τ ≺ n (D12). -/
theorem not_sink_prec {s : SW P K} {a : PNode} : ¬ s.Prec .sink a := by
  intro h
  have h₁ := h.nodeRank_lt
  have h₂ := nodeRank_le s a
  rw [show s.nodeRank .sink = s.nLeaves + 1 from rfl] at h₁
  omega

/-- σ ≺ τ (through any node instance — the term is nonempty, 1.1). -/
theorem src_prec_sink (s : SW P K) : s.Prec .src .sink :=
  Relation.TransGen.head (Gen.fromSrc (i := 0) (nLeaves_pos s))
    (Relation.TransGen.single (Gen.toSink (nLeaves_pos s)))

/-! ### Embedding ≺ of a subterm into ≺ of the composite -/

/-- Generic transitive-closure map: a node relabeling that maps generators
to generators maps ≺ to ≺.  Every embedding below is defined solely by its
generator mapping. -/
theorem prec_map {t t' : SW P K} {f : PNode → PNode}
    (hf : ∀ a b, t.Gen a b → t'.Gen (f a) (f b)) {a b : PNode}
    (h : t.Prec a b) : t'.Prec (f a) (f b) := by
  induction h with
  | single hg => exact Relation.TransGen.single (hf _ _ hg)
  | tail _ hg ih => exact Relation.TransGen.tail ih (hf _ _ hg)

theorem gen_embed_seriesL {s₁ s₂ : SW P K} {a b : PNode} (h : Gen s₁ a b) :
    Gen (SW.series s₁ s₂) a b := by
  cases h with
  | struct hs => exact .struct (.seriesLeft hs)
  | fromSrc hi => exact .fromSrc (by rw [nLeaves_series]; omega)
  | toSink hi => exact .toSink (by rw [nLeaves_series]; omega)

theorem gen_embed_seriesR {s₁ s₂ : SW P K} {a b : PNode} (h : Gen s₂ a b) :
    Gen (SW.series s₁ s₂) (a.shift s₁.nLeaves) (b.shift s₁.nLeaves) := by
  cases h with
  | struct hs => exact .struct (.seriesRight hs)
  | fromSrc hi => exact .fromSrc (by rw [nLeaves_series]; omega)
  | toSink hi => exact .toSink (by rw [nLeaves_series]; omega)

theorem gen_embed_parL {m : Mode} {s₁ s₂ : SW P K} {a b : PNode}
    (h : Gen s₁ a b) : Gen (SW.par m s₁ s₂) a b := by
  cases h with
  | struct hs => exact .struct (.parLeft hs)
  | fromSrc hi => exact .fromSrc (by rw [nLeaves_par]; omega)
  | toSink hi => exact .toSink (by rw [nLeaves_par]; omega)

theorem gen_embed_parR {m : Mode} {s₁ s₂ : SW P K} {a b : PNode}
    (h : Gen s₂ a b) :
    Gen (SW.par m s₁ s₂) (a.shift s₁.nLeaves) (b.shift s₁.nLeaves) := by
  cases h with
  | struct hs => exact .struct (.parRight hs)
  | fromSrc hi => exact .fromSrc (by rw [nLeaves_par]; omega)
  | toSink hi => exact .toSink (by rw [nLeaves_par]; omega)

theorem prec_embed_seriesL {s₁ s₂ : SW P K} {a b : PNode} (h : s₁.Prec a b) :
    (SW.series s₁ s₂).Prec a b :=
  prec_map (f := id) (fun _ _ => gen_embed_seriesL) h

theorem prec_embed_seriesR {s₁ s₂ : SW P K} {a b : PNode} (h : s₂.Prec a b) :
    (SW.series s₁ s₂).Prec (a.shift s₁.nLeaves) (b.shift s₁.nLeaves) :=
  prec_map (fun _ _ => gen_embed_seriesR) h

theorem prec_embed_parL {m : Mode} {s₁ s₂ : SW P K} {a b : PNode}
    (h : s₁.Prec a b) : (SW.par m s₁ s₂).Prec a b :=
  prec_map (f := id) (fun _ _ => gen_embed_parL) h

theorem prec_embed_parR {m : Mode} {s₁ s₂ : SW P K} {a b : PNode}
    (h : s₂.Prec a b) :
    (SW.par m s₁ s₂).Prec (a.shift s₁.nLeaves) (b.shift s₁.nLeaves) :=
  prec_map (fun _ _ => gen_embed_parR) h

/-! ### ≺ only depends on the SP structure, not on bindings -/

theorem sgen_rebind {s : SW P K} (θ : Subst P K) {i j : ℕ} (h : SGen s i j) :
    SGen (s.rebind θ) i j := by
  induction h with
  | @seriesCross s₁ s₂ i j h₁ h₂ =>
      have h' := SGen.seriesCross (s₁ := s₁.rebind θ) (s₂ := s₂.rebind θ)
        (i := i) (j := j) (by rwa [nLeaves_rebind]) (by rwa [nLeaves_rebind])
      rw [nLeaves_rebind] at h'
      exact h'
  | @seriesLeft s₁ s₂ i j h ih => exact .seriesLeft ih
  | @seriesRight s₁ s₂ i j h ih =>
      have h' := SGen.seriesRight (s₁ := s₁.rebind θ) (s₂ := s₂.rebind θ) ih
      rw [nLeaves_rebind] at h'
      exact h'
  | @parCross12 s₁ s₂ i j h₁ h₂ =>
      have h' := SGen.parCross12 (s₁ := s₁.rebind θ) (s₂ := s₂.rebind θ)
        (i := i) (j := j) (by rwa [nLeaves_rebind]) (by rwa [nLeaves_rebind])
      rw [nLeaves_rebind] at h'
      exact h'
  | @parCross21 s₁ s₂ i j h₁ h₂ =>
      have h' := SGen.parCross21 (s₁ := s₁.rebind θ) (s₂ := s₂.rebind θ)
        (i := i) (j := j) (by rwa [nLeaves_rebind]) (by rwa [nLeaves_rebind])
      rw [nLeaves_rebind] at h'
      exact h'
  | @parLeft m s₁ s₂ i j h ih => exact .parLeft ih
  | @parRight m s₁ s₂ i j h ih =>
      have h' := SGen.parRight (m := m) (s₁ := s₁.rebind θ) (s₂ := s₂.rebind θ) ih
      rw [nLeaves_rebind] at h'
      exact h'

theorem gen_rebind {s : SW P K} (θ : Subst P K) {a b : PNode} (h : Gen s a b) :
    Gen (s.rebind θ) a b := by
  cases h with
  | struct hs => exact .struct (sgen_rebind θ hs)
  | fromSrc hi => exact .fromSrc (by rwa [nLeaves_rebind])
  | toSink hi => exact .toSink (by rwa [nLeaves_rebind])

theorem prec_rebind {s : SW P K} (θ : Subst P K) {a b : PNode}
    (h : s.Prec a b) : (s.rebind θ).Prec a b :=
  prec_map (f := id) (fun _ _ => gen_rebind θ) h

end SW

/-! ## Producers and consumers (4.2/4.4, node side) -/

/-- Instance `i` of `s` has an input slot resolving to `a`. -/
def ConsumesAt (s : SW P K) (i : ℕ) (a : Alloc P K) : Prop :=
  AtIdx s.leaves i (fun l => a ∈ l.inputs)

/-- Instance `i` of `s` mints `k` (at a fresh output slot). -/
def MintsAt (s : SW P K) (i : ℕ) (k : K) : Prop :=
  AtIdx s.leaves i (fun l => k ∈ l.minted)

/-- The *true producer* node of an allocation (4.2): σ for a parameter
(adoption, not minting — contents caller-provided), the minting instance for
a produced ID. -/
def IsProducer (s : SW P K) : Alloc P K → PNode → Prop
  | .param _, n => n = .src
  | .prod k, n => ∃ i, n = .inst i ∧ MintsAt s i k

theorem ConsumesAt.lt_nLeaves {s : SW P K} {i : ℕ} {a : Alloc P K}
    (h : ConsumesAt s i a) : i < s.nLeaves :=
  AtIdx.lt_length h

theorem MintsAt.lt_nLeaves {s : SW P K} {i : ℕ} {k : K}
    (h : MintsAt s i k) : i < s.nLeaves :=
  AtIdx.lt_length h

theorem MintsAt.mem_minted {s : SW P K} {i : ℕ} {k : K} (h : MintsAt s i k) :
    k ∈ s.forget.minted := by
  obtain ⟨l, hl, hk⟩ := h
  exact W.mem_minted_iff_leaves.mpr
    ⟨l, by rw [SW.leaves_forget]; exact List.mem_of_getElem? hl, hk⟩

theorem ConsumesAt.mem_buffers {s : SW P K} {i : ℕ} {a : Alloc P K}
    (h : ConsumesAt s i a) : a ∈ s.forget.buffers := by
  obtain ⟨l, hl, ha⟩ := h
  exact W.mem_buffers_iff_leaves.mpr
    ⟨l, by rw [SW.leaves_forget]; exact List.mem_of_getElem? hl, Or.inl ha⟩

theorem mintsAt_rebind {s : SW P K} {θ : Subst P K} {i : ℕ} {k : K} :
    MintsAt (s.rebind θ) i k ↔ MintsAt s i k := by
  unfold MintsAt
  rw [SW.leaves_rebind, atIdx_map]
  simp only [LeafInst.minted_rebind]

/-! ### Branch-local decomposition API

Composite occurrences decompose through the lemmas below; downstream proofs
never unfold `AtIdx`/`MintsAt`/`ConsumesAt` directly.  The ℕ-offset index
arithmetic of the occurrence representation is quarantined here: future
changes to the occurrence representation go through these lemmas only. -/

@[simp] theorem SW.length_leaves (s : SW P K) : s.leaves.length = s.nLeaves :=
  rfl

theorem mintsAt_two_arms {s t₁ t₂ : SW P K}
    (hs : s.leaves = t₁.leaves ++ t₂.leaves) {i : ℕ} {k : K} :
    MintsAt s i k ↔
      (i < t₁.nLeaves ∧ MintsAt t₁ i k) ∨
      (t₁.nLeaves ≤ i ∧ MintsAt t₂ (i - t₁.nLeaves) k) := by
  unfold MintsAt
  rw [hs, atIdx_append, SW.length_leaves]

theorem consumesAt_two_arms {s t₁ t₂ : SW P K}
    (hs : s.leaves = t₁.leaves ++ t₂.leaves) {i : ℕ} {a : Alloc P K} :
    ConsumesAt s i a ↔
      (i < t₁.nLeaves ∧ ConsumesAt t₁ i a) ∨
      (t₁.nLeaves ≤ i ∧ ConsumesAt t₂ (i - t₁.nLeaves) a) := by
  unfold ConsumesAt
  rw [hs, atIdx_append, SW.length_leaves]

theorem mintsAt_series_iff {s₁ s₂ : SW P K} {i : ℕ} {k : K} :
    MintsAt (.series s₁ s₂) i k ↔
      (i < s₁.nLeaves ∧ MintsAt s₁ i k) ∨
      (s₁.nLeaves ≤ i ∧ MintsAt s₂ (i - s₁.nLeaves) k) :=
  mintsAt_two_arms rfl

theorem mintsAt_par_iff {m : Mode} {s₁ s₂ : SW P K} {i : ℕ} {k : K} :
    MintsAt (.par m s₁ s₂) i k ↔
      (i < s₁.nLeaves ∧ MintsAt s₁ i k) ∨
      (s₁.nLeaves ≤ i ∧ MintsAt s₂ (i - s₁.nLeaves) k) :=
  mintsAt_two_arms rfl

theorem consumesAt_series_iff {s₁ s₂ : SW P K} {i : ℕ} {a : Alloc P K} :
    ConsumesAt (.series s₁ s₂) i a ↔
      (i < s₁.nLeaves ∧ ConsumesAt s₁ i a) ∨
      (s₁.nLeaves ≤ i ∧ ConsumesAt s₂ (i - s₁.nLeaves) a) :=
  consumesAt_two_arms rfl

theorem consumesAt_par_iff {m : Mode} {s₁ s₂ : SW P K} {i : ℕ} {a : Alloc P K} :
    ConsumesAt (.par m s₁ s₂) i a ↔
      (i < s₁.nLeaves ∧ ConsumesAt s₁ i a) ∨
      (s₁.nLeaves ≤ i ∧ ConsumesAt s₂ (i - s₁.nLeaves) a) :=
  consumesAt_two_arms rfl

/-- A rebound instance consumes exactly the θ-images of what the original
consumes. -/
theorem consumesAt_rebind_iff {s : SW P K} {θ : Subst P K} {i : ℕ}
    {a : Alloc P K} :
    ConsumesAt (s.rebind θ) i a ↔ ∃ b, ConsumesAt s i b ∧ θ.apply b = a := by
  unfold ConsumesAt
  rw [SW.leaves_rebind, atIdx_map]
  constructor
  · rintro ⟨l, hl, hmem⟩
    rw [LeafInst.inputs_rebind] at hmem
    obtain ⟨b, hb, hab⟩ := hmem
    exact ⟨b, ⟨l, hl, hb⟩, hab⟩
  · rintro ⟨b, ⟨l, hl, hb⟩, hab⟩
    refine ⟨l, hl, ?_⟩
    show a ∈ (l.rebind θ).inputs
    rw [LeafInst.inputs_rebind]
    exact ⟨b, hb, hab⟩

/-- Mint disjointness transports across rebinding of the right operand
(rebinding never touches mint names). -/
theorem MintDisjoint.rebind_right {s₁ s₂ : SW P K} (θ : Subst P K)
    (hd : MintDisjoint s₁.forget s₂.forget) :
    MintDisjoint s₁.forget (s₂.rebind θ).forget :=
  fun k h1 h2 => hd k h1 (by simpa using h2)

/-- Under operand mint disjointness, a composite `MintsAt` resolves to the
arm whose `minted` set contains the ID (left case). -/
theorem MintsAt.resolve_left {s t₁ t₂ : SW P K}
    (hs : s.leaves = t₁.leaves ++ t₂.leaves)
    (hd : MintDisjoint t₁.forget t₂.forget) {i : ℕ} {k : K}
    (h : MintsAt s i k) (hk : k ∈ t₁.forget.minted) :
    i < t₁.nLeaves ∧ MintsAt t₁ i k := by
  rcases (mintsAt_two_arms hs).mp h with ⟨hi, hm⟩ | ⟨hi, hm⟩
  · exact ⟨hi, hm⟩
  · exact (hd k hk hm.mem_minted).elim

/-- Right case of `MintsAt.resolve_left`. -/
theorem MintsAt.resolve_right {s t₁ t₂ : SW P K}
    (hs : s.leaves = t₁.leaves ++ t₂.leaves)
    (hd : MintDisjoint t₁.forget t₂.forget) {i : ℕ} {k : K}
    (h : MintsAt s i k) (hk : k ∈ t₂.forget.minted) :
    t₁.nLeaves ≤ i ∧ MintsAt t₂ (i - t₁.nLeaves) k := by
  rcases (mintsAt_two_arms hs).mp h with ⟨hi, hm⟩ | ⟨hi, hm⟩
  · exact (hd k hm.mem_minted hk).elim
  · exact ⟨hi, hm⟩

/-- Under operand mint disjointness, the minting side is *determined* by
which arm's `minted` set contains the ID. -/
theorem mintsAt_left_iff_mem_minted {s t₁ t₂ : SW P K}
    (hs : s.leaves = t₁.leaves ++ t₂.leaves)
    (hd : MintDisjoint t₁.forget t₂.forget) {i : ℕ} {k : K}
    (h : MintsAt s i k) :
    (i < t₁.nLeaves ∧ MintsAt t₁ i k) ↔ k ∈ t₁.forget.minted :=
  ⟨fun ⟨_, hm⟩ => hm.mem_minted, h.resolve_left hs hd⟩

/-- Every minted ID has a minting instance. -/
theorem exists_mintsAt {s : SW P K} {k : K} (hk : k ∈ s.forget.minted) :
    ∃ i, MintsAt s i k := by
  rw [W.mem_minted_iff_leaves, SW.leaves_forget] at hk
  obtain ⟨l, hl, hkl⟩ := hk
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  exact ⟨i, l, hi, hkl⟩

/-- Every allocation occurring in a well-formed scheduled term has a
producer node (σ for parameters — 4.2 makes the finalized graph closed;
the minting instance for produced IDs — D4). -/
theorem SWF.exists_producer {s : SW P K} (hs : SWF s) {a : Alloc P K}
    (ha : a ∈ s.forget.buffers) : ∃ n, IsProducer s a n := by
  cases a with
  | param p => exact ⟨.src, rfl⟩
  | prod k =>
      obtain ⟨i, hi⟩ :=
        exists_mintsAt (hs.forget_wf.mem_minted_of_prod_mem_buffers k ha)
      exact ⟨.inst i, i, rfl, hi⟩

/-- **D7** (unique true producer): a produced ID is minted by at most one
node instance.  With 3.1 (only fresh outputs are written), no allocation has
more than one writer — "same allocation, new contents" has no syntax. -/
theorem SWF.mintsAt_unique {s : SW P K} (hs : SWF s) :
    ∀ {i i' : ℕ} {k : K}, MintsAt s i k → MintsAt s i' k → i = i' := by
  induction hs with
  | @leaf l hβ hm =>
      intro i i' k h h'
      have h₁ := h.lt_nLeaves
      have h₂ := h'.lt_nLeaves
      rw [SW.nLeaves_leaf] at h₁ h₂
      omega
  | @series s₁ s₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro i i' k h h'
      rw [mintsAt_series_iff] at h h'
      rcases h with ⟨hi, h⟩ | ⟨hi, h⟩ <;> rcases h' with ⟨hi', h'⟩ | ⟨hi', h'⟩
      · exact ih₁ h h'
      · exact (hd k h.mem_minted (mintsAt_rebind.mp h').mem_minted).elim
      · exact (hd k h'.mem_minted (mintsAt_rebind.mp h).mem_minted).elim
      · have := ih₂ (mintsAt_rebind.mp h) (mintsAt_rebind.mp h')
        omega
  | @par m s₁ s₂ h₁ h₂ hd ih₁ ih₂ =>
      intro i i' k h h'
      rw [mintsAt_par_iff] at h h'
      rcases h with ⟨hi, h⟩ | ⟨hi, h⟩ <;> rcases h' with ⟨hi', h'⟩ | ⟨hi', h'⟩
      · exact ih₁ h h'
      · exact (hd k h.mem_minted h'.mem_minted).elim
      · exact (hd k h'.mem_minted h.mem_minted).elim
      · have := ih₂ h h'
        omega

/-! ## D9: dataflow respects ≺ -/

/-- **D9** (instance consumers): for every allocation `a` and every node
instance `c` with an input slot resolving to `a`: `producer(a) ≺ c`.

Spec proof shape, followed exactly: a slot's value is either its leaf
parameter — produced by σ, and σ ≺ c by the endpoint generators — or was set
produced-valued by exactly one Series substitution whose range lies in the
left arm's outputs while `c` sits in the right arm, so the Series clause
gives `producer ≺ c`; passthrough creates no new consumers.  (D4: bindings,
once produced-valued, are final, so the inner inductive hypotheses transport
along the embeddings of ≺.) -/
theorem SWF.producer_prec_consumer {s : SW P K} (hs : SWF s) :
    ∀ {i : ℕ} {a : Alloc P K} {n : PNode},
      ConsumesAt s i a → IsProducer s a n → s.Prec n (.inst i) := by
  induction hs with
  | @leaf l hβ hm =>
      intro i a n hc hp
      have hi : i < 1 := by
        have := hc.lt_nLeaves; rwa [SW.nLeaves_leaf] at this
      obtain ⟨l', hl', ha⟩ := hc
      have hi0 : i = 0 := by omega
      subst hi0
      have hll : l' = l := by
        simp only [SW.leaves_leaf] at hl'
        simpa using hl'.symm
      subst hll
      obtain ⟨j, hj⟩ := ha
      cases a with
      | param p =>
          simp only [IsProducer] at hp
          subst hp
          exact Relation.TransGen.single
            (SW.Gen.fromSrc (by rw [SW.nLeaves_leaf]; omega))
      | prod k =>
          have := hβ j
          rw [hj] at this
          cases this
  | @series s₁ s₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro i a n hc hp
      have hwf₁ := h₁.forget_wf
      have hwf₂ := h₂.forget_wf
      have hpd : θ.ParamDom := hθ.paramDom hwf₂
      have htotal : (SW.series s₁ (s₂.rebind θ)).nLeaves =
          s₁.nLeaves + s₂.nLeaves := by
        rw [SW.nLeaves_series, SW.nLeaves_rebind]
      rw [consumesAt_series_iff] at hc
      rcases hc with ⟨hi, hc₁⟩ | ⟨hi, hc⟩
      · -- consumer in the left arm; its binding is untouched by θ
        cases a with
        | param p =>
            simp only [IsProducer] at hp
            subst hp
            exact Relation.TransGen.single (SW.Gen.fromSrc
              (by rw [htotal]; omega))
        | prod k =>
            simp only [IsProducer] at hp
            obtain ⟨i₀, rfl, hm⟩ := hp
            have hm₁ := (hm.resolve_left rfl (hd.rebind_right θ)
              (hwf₁.mem_minted_of_prod_mem_buffers k hc₁.mem_buffers)).2
            exact SW.prec_embed_seriesL (ih₁ hc₁ ⟨i₀, rfl, hm₁⟩)
      · -- consumer in the (rewritten) right arm
        obtain ⟨b, hc₂, hab⟩ := consumesAt_rebind_iff.mp hc
        have hi₂ : i - s₁.nLeaves < s₂.nLeaves := hc₂.lt_nLeaves
        cases b with
        | prod k' =>
            -- produced-valued binding: untouched by θ (D4); producer inside s₂
            rw [hpd.apply_prod] at hab
            subst hab
            simp only [IsProducer] at hp
            obtain ⟨i₀, rfl, hm⟩ := hp
            obtain ⟨hge₀, hmr⟩ := hm.resolve_right rfl (hd.rebind_right θ)
              (by simpa using hwf₂.mem_minted_of_prod_mem_buffers k' hc₂.mem_buffers)
            -- ih₂ orders producer before consumer inside s₂; ≺ depends only
            -- on the SP structure, so it transports along rebind, then
            -- embeds into the composite (shifted by n₁)
            have hprec := SW.prec_embed_seriesR (s₁ := s₁) (s₂ := s₂.rebind θ)
              (SW.prec_rebind θ
                (ih₂ hc₂ ⟨i₀ - s₁.nLeaves, rfl, mintsAt_rebind.mp hmr⟩))
            have e₀ : s₁.nLeaves + (i₀ - s₁.nLeaves) = i₀ := by omega
            have e₁ : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
            simpa [PNode.shift, e₀, e₁] using hprec
        | param q =>
            -- parameter binding: rewritten by θ into outputs(W₁)
            have hqi : Alloc.param q ∈ s₂.forget.inputs :=
              hwf₂.param_mem_inputs_of_mem_buffers q hc₂.mem_buffers
            obtain ⟨c, hcq⟩ := Option.isSome_iff_exists.mp ((hθ.dom_eq _).mpr hqi)
            rw [θ.apply_of_some hcq] at hab
            subst hab
            have hco : c ∈ s₁.forget.outputs := hθ.codom _ _ hcq
            cases c with
            | param p =>
                simp only [IsProducer] at hp
                subst hp
                exact Relation.TransGen.single (SW.Gen.fromSrc
                  (by rw [htotal]; omega))
            | prod k =>
                -- producer in the left arm; the Series clause gives the order
                simp only [IsProducer] at hp
                obtain ⟨i₀, rfl, hm⟩ := hp
                obtain ⟨hi₀, -⟩ := hm.resolve_left rfl (hd.rebind_right θ)
                  (hwf₁.mem_minted_of_prod_mem_buffers k
                    (s₁.forget.outputs_subset_buffers hco))
                have hcross : SW.SGen (SW.series s₁ (s₂.rebind θ)) i₀
                    (s₁.nLeaves + (i - s₁.nLeaves)) :=
                  SW.SGen.seriesCross hi₀ (by rwa [SW.nLeaves_rebind])
                have e₁ : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
                rw [e₁] at hcross
                exact Relation.TransGen.single (SW.Gen.struct hcross)
  | @par m s₁ s₂ h₁ h₂ hd ih₁ ih₂ =>
      intro i a n hc hp
      have hwf₁ := h₁.forget_wf
      have hwf₂ := h₂.forget_wf
      rw [consumesAt_par_iff] at hc
      rcases hc with ⟨hi, hc₁⟩ | ⟨hi, hc₂⟩
      · cases a with
        | param p =>
            simp only [IsProducer] at hp
            subst hp
            exact Relation.TransGen.single (SW.Gen.fromSrc
              (by rw [SW.nLeaves_par]; omega))
        | prod k =>
            simp only [IsProducer] at hp
            obtain ⟨i₀, rfl, hm⟩ := hp
            have hm₁ := (hm.resolve_left rfl hd
              (hwf₁.mem_minted_of_prod_mem_buffers k hc₁.mem_buffers)).2
            exact SW.prec_embed_parL (ih₁ hc₁ ⟨i₀, rfl, hm₁⟩)
      · cases a with
        | param p =>
            simp only [IsProducer] at hp
            subst hp
            have := hc₂.lt_nLeaves
            exact Relation.TransGen.single (SW.Gen.fromSrc
              (by rw [SW.nLeaves_par]; omega))
        | prod k =>
            simp only [IsProducer] at hp
            obtain ⟨i₀, rfl, hm⟩ := hp
            obtain ⟨hge₀, hm₂⟩ := hm.resolve_right rfl hd
              (hwf₂.mem_minted_of_prod_mem_buffers k hc₂.mem_buffers)
            have hprec := SW.prec_embed_parR (m := m) (s₁ := s₁)
              (ih₂ hc₂ ⟨i₀ - s₁.nLeaves, rfl, hm₂⟩)
            have e₀ : s₁.nLeaves + (i₀ - s₁.nLeaves) = i₀ := by omega
            have e₁ : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
            simpa [PNode.shift, e₀, e₁] using hprec

/-- **D9** (sentinel sink): `producer(a) ≺ τ` — by the `(n, τ)` generators
when the producer is an instance, and σ ≺ τ through any node of the
(nonempty) term when the producer is σ. -/
theorem producer_prec_sink {s : SW P K} {a : Alloc P K} {n : PNode}
    (hp : IsProducer s a n) : s.Prec n .sink := by
  cases a with
  | param p =>
      simp only [IsProducer] at hp
      subst hp
      exact SW.src_prec_sink s
  | prod k =>
      simp only [IsProducer] at hp
      obtain ⟨i, rfl, hm⟩ := hp
      exact Relation.TransGen.single (SW.Gen.toSink hm.lt_nLeaves)

end WorkGraph
