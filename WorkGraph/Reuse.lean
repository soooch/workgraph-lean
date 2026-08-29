/-
# Work Graph Model — Stage 5: Reuse legality (D14, with D6 en route)

Proves the memory-reuse payoff of the model (D14):

* **Series reuse** (`SWF.series_not_mayOverlap_internal_fresh`): in
  `Series(W₁, W₂)`, an internal allocation of the left arm never conflicts
  with a fresh allocation of the right arm — *all of `internal(W₁)` is
  reusable by every fresh allocation in W₂*.  The proof runs exactly along
  the spec's D6 + D13/4.3 route: every user of `a ∈ internal(W₁)` is a node
  of W₁ (D6: the producer by D4, consumers because a right-arm binding is
  either a W₂-minted ID — excluded by global distinctness — or θ-rewritten
  into `outputs(W₁)` — excluded by internality; τ is excluded because
  internality survives into the composite by D5), and the Series clause of
  4.3 orders all of W₁ — dead ends included (D13) — before the right-arm
  producer.

* **Sequentialized-Par reuse** (`SWF.par12_not_mayOverlap_internal_fresh`,
  `SWF.par21_not_mayOverlap_internal_fresh`): the same for `Par` in modes
  `seq(1,2)` and `seq(2,1)` — the earlier branch's internal buffers are
  reusable by the later branch.

* **No concurrent cross-branch reuse**: no order crosses a concurrent Par —
  at the root (`SW.conc_prec_side`) and, contextually, for a concurrent Par
  anywhere inside a larger composite (`SW.ConcBlock.not_cross_prec`, via
  block-descent of ≺-paths: every generator into or out of a Par arm's
  index block either stays in the block or hits a sentinel, so a cross path
  would need a node both before and after the block).  Hence fresh
  allocations of opposite branches always conflict at the root
  (`SWF.conc_mayOverlap_fresh`), and in general *any* two allocations with
  users on opposite branches of any concurrent Par conflict
  (`SWF.conc_mayOverlap_of_cross_users`) — covering allocations injected
  into a branch by an enclosing Series as well as branch-local fresh ones.
-/
import WorkGraph.Arena

namespace WorkGraph

variable {P K : Type*}

/-! ## ≺ never crosses a concurrent Par -/

theorem SW.sgen_conc_side {s₁ s₂ : SW P K} {i j : ℕ}
    (h : SW.SGen (SW.par .conc s₁ s₂) i j) :
    (i < s₁.nLeaves ↔ j < s₁.nLeaves) := by
  cases h with
  | parLeft h =>
      obtain ⟨hi, hj⟩ := h.bounds
      constructor <;> intro <;> assumption
  | parRight h =>
      constructor <;> intro <;> omega

/-- Instances on opposite sides of a concurrent Par are ≺-incomparable
(D14: "concurrent Par branches admit no cross-branch reuse — no order
exists between them"). -/
theorem SW.conc_prec_side {s₁ s₂ : SW P K} {a b : PNode}
    (h : (SW.par .conc s₁ s₂).Prec a b) :
    ∀ i j, a = .inst i → b = .inst j → (i < s₁.nLeaves ↔ j < s₁.nLeaves) := by
  induction h with
  | single hg =>
      intro i j ha hb
      subst ha; subst hb
      cases hg with
      | struct hs => exact sgen_conc_side hs
  | tail hab hbc ih =>
      intro i j ha hb
      subst ha; subst hb
      cases hbc with
      | struct hs =>
          exact (ih _ _ rfl rfl).trans (sgen_conc_side hs)
      | fromSrc h' =>
          exact absurd hab SW.not_prec_src

/-! ## D14: Series reuse -/

/-- **D14 (Series)**: `a ∈ internal(W₁)` never conflicts with a fresh
allocation of the right arm — `internal(W₁)` is fully reusable past the
Series boundary. -/
theorem SWF.series_not_mayOverlap_internal_fresh {s₁ s₂ : SW P K}
    {θ : Subst P K} (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hθ : ThetaFits θ s₁.forget s₂.forget)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal)
    {k : K} (hk : k ∈ s₂.forget.minted) :
    ¬ MayOverlap (SW.series s₁ (s₂.rebind θ)) a (.prod k) := by
  set s : SW P K := SW.series s₁ (s₂.rebind θ) with hs_def
  have hswf : SWF s := SWF.series h₁ h₂ hθ hd
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  have hpd : θ.ParamDom := hθ.paramDom hwf₂
  have hlen : s₁.leaves.length = s₁.nLeaves := rfl
  obtain ⟨hb, hni, hno⟩ := ha
  -- a is a produced ID minted in the left arm (D3 + D4)
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₁.param_mem_inputs_of_mem_buffers p hb) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₁ : k' ∈ s₁.forget.minted := hwf₁.mem_minted_of_prod_mem_buffers k' hb
  -- the forgotten composite is the spec Series composite
  have hforget : s.forget = s₁.forget.mkSeries s₂.forget θ := by
    simp [hs_def, W.mkSeries]
  -- internality survives into the composite (D5), so τ is not a user of a
  have hint : Alloc.prod k' ∈ s.forget.internal := by
    rw [hforget, hwf₁.internal_mkSeries hwf₂ hθ hd]
    exact Or.inl (Or.inl ⟨hb, hni, hno⟩)
  -- every user of a is an instance of the left arm (D6)
  have huser : ∀ n, IsUser s (Alloc.prod k') n → ∃ i, n = .inst i ∧ i < s₁.nLeaves := by
    rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
    · -- the producer: its minting instance, in the left arm by distinctness
      obtain ⟨i₀, rfl, hm⟩ := hp
      refine ⟨i₀, rfl, ?_⟩
      unfold MintsAt at hm
      rw [hs_def, SW.leaves_series, atIdx_append] at hm
      rcases hm with ⟨hi₀, _⟩ | ⟨_, hm⟩
      · rwa [hlen] at hi₀
      · exfalso
        rw [SW.leaves_rebind, atIdx_map] at hm
        simp only [LeafInst.minted_rebind] at hm
        exact hd k' hk'₁ (MintsAt.mem_minted hm)
    · -- a consumer: a right-arm slot cannot resolve to a (D4 + internality)
      refine ⟨i, rfl, ?_⟩
      unfold ConsumesAt at hc
      rw [hs_def, SW.leaves_series, atIdx_append] at hc
      rcases hc with ⟨hi, _⟩ | ⟨_, hc⟩
      · rwa [hlen] at hi
      · exfalso
        rw [SW.leaves_rebind, atIdx_map] at hc
        obtain ⟨l₂, hl₂, hmem⟩ := hc
        rw [LeafInst.inputs_rebind] at hmem
        obtain ⟨b₀, hb₀, hab⟩ := hmem
        have hc₂ : ConsumesAt s₂ _ b₀ := ⟨l₂, hl₂, hb₀⟩
        cases b₀ with
        | prod k₀ =>
            rw [hpd.apply_prod] at hab
            cases hab
            exact hd k' hk'₁
              (hwf₂.mem_minted_of_prod_mem_buffers k' hc₂.mem_buffers)
        | param q =>
            have hqi : Alloc.param q ∈ s₂.forget.inputs :=
              hwf₂.param_mem_inputs_of_mem_buffers q hc₂.mem_buffers
            obtain ⟨c, hcq⟩ := Option.isSome_iff_exists.mp ((hθ.dom_eq _).mpr hqi)
            rw [θ.apply_of_some hcq] at hab
            subst hab
            exact hno (hθ.codom _ _ hcq)
    · -- τ: excluded, a is internal to the composite
      exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)
  -- the producer of the fresh right-arm allocation sits in the right arm
  intro hov
  refine hov.1 ?_
  rintro n hn m hm
  obtain ⟨i, rfl, hi⟩ := huser n hn
  obtain ⟨i₀, rfl, hm⟩ := hm
  have hlt := hm.lt_nLeaves
  have hm₂ : s₁.nLeaves ≤ i₀ := by
    unfold MintsAt at hm
    rw [hs_def, SW.leaves_series, atIdx_append] at hm
    rcases hm with ⟨_, hm⟩ | ⟨hi₀, _⟩
    · exact absurd (hd k (MintsAt.mem_minted hm) hk) not_false
    · rwa [hlen] at hi₀
  -- the Series clause of 4.3 orders all of W₁ before every node of W₂ (D13)
  have hcross : SW.SGen s i (s₁.nLeaves + (i₀ - s₁.nLeaves)) := by
    rw [hs_def]
    refine SW.SGen.seriesCross hi ?_
    rw [hs_def, SW.nLeaves_series] at hlt
    omega
  have e : s₁.nLeaves + (i₀ - s₁.nLeaves) = i₀ := by omega
  rw [e] at hcross
  exact Relation.TransGen.single (SW.Gen.struct hcross)

/-! ## D14: sequentialized-Par reuse -/

/-- **D14 (sequentialized Par, `seq(1,2)`)**: an internal allocation of the
first branch never conflicts with a fresh allocation of the second —
internal buffers of the earlier branch are reusable by the later one.
(The `seq(2,1)` mirror is `SWF.par21_not_mayOverlap_internal_fresh`.) -/
theorem SWF.par12_not_mayOverlap_internal_fresh {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal)
    {k : K} (hk : k ∈ s₂.forget.minted) :
    ¬ MayOverlap (SW.par .seq12 s₁ s₂) a (.prod k) := by
  set s : SW P K := SW.par .seq12 s₁ s₂ with hs_def
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  have hlen : s₁.leaves.length = s₁.nLeaves := rfl
  obtain ⟨hb, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₁.param_mem_inputs_of_mem_buffers p hb) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₁ : k' ∈ s₁.forget.minted := hwf₁.mem_minted_of_prod_mem_buffers k' hb
  -- internality survives into the composite (D5 for Par)
  have hint : Alloc.prod k' ∈ s.forget.internal := by
    have : s.forget = W.par s₁.forget s₂.forget := rfl
    rw [this, hwf₁.internal_par hwf₂ hd]
    exact Or.inl ⟨hb, hni, hno⟩
  have huser : ∀ n, IsUser s (Alloc.prod k') n → ∃ i, n = .inst i ∧ i < s₁.nLeaves := by
    rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
    · obtain ⟨i₀, rfl, hm⟩ := hp
      refine ⟨i₀, rfl, ?_⟩
      unfold MintsAt at hm
      rw [hs_def, SW.leaves_par, atIdx_append] at hm
      rcases hm with ⟨hi₀, _⟩ | ⟨_, hm⟩
      · rwa [hlen] at hi₀
      · exact absurd (hd k' hk'₁ (MintsAt.mem_minted hm)) not_false
    · refine ⟨i, rfl, ?_⟩
      unfold ConsumesAt at hc
      rw [hs_def, SW.leaves_par, atIdx_append] at hc
      rcases hc with ⟨hi, _⟩ | ⟨_, hc⟩
      · rwa [hlen] at hi
      · exfalso
        have hc₂ : ConsumesAt s₂ _ (Alloc.prod k') := hc
        exact hd k' hk'₁
          (hwf₂.mem_minted_of_prod_mem_buffers k' hc₂.mem_buffers)
    · exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)
  intro hov
  refine hov.1 ?_
  rintro n hn m hm
  obtain ⟨i, rfl, hi⟩ := huser n hn
  obtain ⟨i₀, rfl, hm⟩ := hm
  have hlt := hm.lt_nLeaves
  have hm₂ : s₁.nLeaves ≤ i₀ := by
    unfold MintsAt at hm
    rw [hs_def, SW.leaves_par, atIdx_append] at hm
    rcases hm with ⟨_, hm⟩ | ⟨hi₀, _⟩
    · exact absurd (hd k (MintsAt.mem_minted hm) hk) not_false
    · rwa [hlen] at hi₀
  have hcross : SW.SGen s i (s₁.nLeaves + (i₀ - s₁.nLeaves)) := by
    rw [hs_def]
    refine SW.SGen.parCross12 hi ?_
    rw [hs_def, SW.nLeaves_par] at hlt
    omega
  have e : s₁.nLeaves + (i₀ - s₁.nLeaves) = i₀ := by omega
  rw [e] at hcross
  exact Relation.TransGen.single (SW.Gen.struct hcross)

/-- **D14 (sequentialized Par, `seq(2,1)`)**: the mirror image — an internal
allocation of the *second* branch (which `seq(2,1)` runs first) never
conflicts with a fresh allocation of the first: internal buffers of the
earlier branch are reusable by the later one, whichever way the Par is
sequentialized. -/
theorem SWF.par21_not_mayOverlap_internal_fresh {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₂.forget.internal)
    {k : K} (hk : k ∈ s₁.forget.minted) :
    ¬ MayOverlap (SW.par .seq21 s₁ s₂) a (.prod k) := by
  set s : SW P K := SW.par .seq21 s₁ s₂ with hs_def
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  have hlen : s₁.leaves.length = s₁.nLeaves := rfl
  obtain ⟨hb, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₂.param_mem_inputs_of_mem_buffers p hb) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₂ : k' ∈ s₂.forget.minted := hwf₂.mem_minted_of_prod_mem_buffers k' hb
  -- internality survives into the composite (D5 for Par)
  have hint : Alloc.prod k' ∈ s.forget.internal := by
    have : s.forget = W.par s₁.forget s₂.forget := rfl
    rw [this, hwf₁.internal_par hwf₂ hd]
    exact Or.inr ⟨hb, hni, hno⟩
  -- every user of a is an instance of the second branch (D6)
  have huser : ∀ n, IsUser s (Alloc.prod k') n →
      ∃ i, n = .inst i ∧ s₁.nLeaves ≤ i ∧ i - s₁.nLeaves < s₂.nLeaves := by
    rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
    · obtain ⟨i₀, rfl, hm⟩ := hp
      refine ⟨i₀, rfl, ?_⟩
      unfold MintsAt at hm
      rw [hs_def, SW.leaves_par, atIdx_append] at hm
      rcases hm with ⟨_, hm⟩ | ⟨hi₀, hm⟩
      · exact absurd (hd k' (MintsAt.mem_minted hm) hk'₂) not_false
      · exact ⟨by rwa [hlen] at hi₀, AtIdx.lt_length hm⟩
    · refine ⟨i, rfl, ?_⟩
      unfold ConsumesAt at hc
      rw [hs_def, SW.leaves_par, atIdx_append] at hc
      rcases hc with ⟨_, hc⟩ | ⟨hi, hc⟩
      · exfalso
        have hc₁ : ConsumesAt s₁ _ (Alloc.prod k') := hc
        exact hd k'
          (hwf₁.mem_minted_of_prod_mem_buffers k' hc₁.mem_buffers) hk'₂
      · exact ⟨by rwa [hlen] at hi, AtIdx.lt_length hc⟩
    · exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)
  intro hov
  refine hov.1 ?_
  rintro n hn m hm
  obtain ⟨i, rfl, hge, hlt₂⟩ := huser n hn
  obtain ⟨i₀, rfl, hm⟩ := hm
  -- the fresh allocation's producer sits in the first branch
  have hm₁ : i₀ < s₁.nLeaves := by
    unfold MintsAt at hm
    rw [hs_def, SW.leaves_par, atIdx_append] at hm
    rcases hm with ⟨hi₀, _⟩ | ⟨_, hm⟩
    · rwa [hlen] at hi₀
    · exact absurd (hd k hk (MintsAt.mem_minted hm)) not_false
  -- the seq(2,1) clause orders all of the second branch before the first
  have hcross : SW.SGen s (s₁.nLeaves + (i - s₁.nLeaves)) i₀ := by
    rw [hs_def]
    exact SW.SGen.parCross21 hlt₂ hm₁
  have e : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
  rw [e] at hcross
  exact Relation.TransGen.single (SW.Gen.struct hcross)

/-! ## D14: no concurrent cross-branch reuse -/

/-- **D14 (concurrent Par)**: fresh allocations of opposite branches of a
concurrent Par always conflict — no order exists between the branches, so
4.5 keeps them address-disjoint. -/
theorem SWF.conc_mayOverlap_fresh {s₁ s₂ : SW P K}
    (hd : MintDisjoint s₁.forget s₂.forget)
    {k₁ k₂ : K} (hk₁ : k₁ ∈ s₁.forget.minted) (hk₂ : k₂ ∈ s₂.forget.minted) :
    MayOverlap (SW.par .conc s₁ s₂) (.prod k₁) (.prod k₂) := by
  set s : SW P K := SW.par .conc s₁ s₂ with hs_def
  have hlen : s₁.leaves.length = s₁.nLeaves := rfl
  -- locate the two producers, on opposite sides
  have hmem₁ : k₁ ∈ s.forget.minted := Or.inl hk₁
  have hmem₂ : k₂ ∈ s.forget.minted := Or.inr hk₂
  obtain ⟨i₁, hm₁⟩ := exists_mintsAt hmem₁
  obtain ⟨i₂, hm₂⟩ := exists_mintsAt hmem₂
  have hside₁ : i₁ < s₁.nLeaves := by
    unfold MintsAt at hm₁
    rw [hs_def, SW.leaves_par, atIdx_append] at hm₁
    rcases hm₁ with ⟨hi, _⟩ | ⟨_, hm⟩
    · rwa [hlen] at hi
    · exact absurd (hd k₁ hk₁ (MintsAt.mem_minted hm)) not_false
  have hside₂ : s₁.nLeaves ≤ i₂ := by
    unfold MintsAt at hm₂
    rw [hs_def, SW.leaves_par, atIdx_append] at hm₂
    rcases hm₂ with ⟨_, hm⟩ | ⟨hi, _⟩
    · exact absurd (hd k₂ (MintsAt.mem_minted hm) hk₂) not_false
    · rwa [hlen] at hi
  have hp₁ : IsProducer s (.prod k₁) (.inst i₁) := ⟨i₁, rfl, hm₁⟩
  have hp₂ : IsProducer s (.prod k₂) (.inst i₂) := ⟨i₂, rfl, hm₂⟩
  constructor
  · intro hall
    have hprec := hall _ hp₁.isUser _ hp₂
    have := SW.conc_prec_side hprec i₁ i₂ rfl rfl
    omega
  · intro hall
    have hprec := hall _ hp₂.isUser _ hp₁
    have := SW.conc_prec_side hprec i₂ i₁ rfl rfl
    omega

/-! ## D14: contextual concurrent Par

`SW.conc_prec_side` treats a concurrent Par at the root.  The lemmas below
extend it to a concurrent Par anywhere in the schedule: a ≺-path between two
instances of one arm of any Series/Par context never leaves that arm's index
block (paths cannot pass through σ or τ, and every structural generator with
an endpoint in the block either stays in the block or crosses in a single
direction fixed by the context — so re-entry is impossible), letting cross
incomparability descend from the designated Par to the full tree. -/

/-- Convert a chain of structural-generator steps back into ≺ of a subtree,
along an index relabeling. -/
theorem SW.transGen_map_prec {t : SW P K} {f : ℕ → ℕ} {r : ℕ → ℕ → Prop}
    (hr : ∀ i j, r i j → t.SGen (f i) (f j)) {i j : ℕ}
    (h : Relation.TransGen r i j) : t.Prec (.inst (f i)) (.inst (f j)) := by
  induction h with
  | single h => exact Relation.TransGen.single (SW.Gen.struct (hr _ _ h))
  | tail _ h ih => exact Relation.TransGen.tail ih (SW.Gen.struct (hr _ _ h))

/-- Generic block descent, predecessor flavor: if every generator *into* a
`B`-instance comes from σ or from a `B`-instance (via `r`), then every
≺-path into a `B`-instance does too. -/
theorem SW.prec_descend_pred {t : SW P K} {B : ℕ → Prop} {r : ℕ → ℕ → Prop}
    (hstep : ∀ x j, t.Gen x (.inst j) → B j →
      x = .src ∨ ∃ i, x = .inst i ∧ B i ∧ r i j)
    {a b : PNode} (h : t.Prec a b) :
    ∀ j, b = .inst j → B j →
      a = .src ∨ ∃ i, a = .inst i ∧ B i ∧ Relation.TransGen r i j := by
  induction h with
  | single hg =>
      intro j hb hBj
      subst hb
      rcases hstep _ _ hg hBj with h | ⟨i, rfl, hBi, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, rfl, hBi, .single hr⟩
  | tail hab hbc ih =>
      intro j hb hBj
      subst hb
      rcases hstep _ _ hbc hBj with rfl | ⟨i', rfl, hBi', hr⟩
      · exact absurd hab SW.not_prec_src
      · rcases ih i' rfl hBi' with h | ⟨i, rfl, hBi, htr⟩
        · exact Or.inl h
        · exact Or.inr ⟨i, rfl, hBi, .tail htr hr⟩

/-- Generic block descent, successor flavor: if every generator *out of* a
`B`-instance goes to τ or to a `B`-instance (via `r`), then every ≺-path out
of a `B`-instance does too. -/
theorem SW.prec_descend_succ {t : SW P K} {B : ℕ → Prop} {r : ℕ → ℕ → Prop}
    (hstep : ∀ i y, t.Gen (.inst i) y → B i →
      y = .sink ∨ ∃ j, y = .inst j ∧ B j ∧ r i j)
    {a b : PNode} (h : t.Prec a b) :
    ∀ i, a = .inst i → B i →
      b = .sink ∨ ∃ j, b = .inst j ∧ B j ∧ Relation.TransGen r i j := by
  induction h with
  | single hg =>
      intro i ha hBi
      subst ha
      rcases hstep _ _ hg hBi with h | ⟨j, rfl, hBj, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, rfl, hBj, .single hr⟩
  | tail hab hbc ih =>
      intro i ha hBi
      subst ha
      rcases ih i rfl hBi with rfl | ⟨j', rfl, hBj', htr⟩
      · cases hbc
      · rcases hstep _ _ hbc hBj' with h | ⟨j, rfl, hBj, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, rfl, hBj, .tail htr hr⟩

/-! Per-context confinement of single generator steps: which side of an arm
boundary a generator can touch is fixed by the constructor and mode. -/

theorem SW.gen_into_seriesL {s₁ s₂ : SW P K} {x : PNode} {j : ℕ}
    (h : SW.Gen (SW.series s₁ s₂) x (.inst j)) (hj : j < s₁.nLeaves) :
    x = .src ∨ ∃ i, x = .inst i ∧ i < s₁.nLeaves ∧ SW.SGen s₁ i j := by
  cases h with
  | struct hs =>
      cases hs with
      | seriesCross h₁ h₂ => exact absurd hj (by omega)
      | seriesLeft h => exact Or.inr ⟨_, rfl, h.bounds.1, h⟩
      | seriesRight h => exact absurd hj (by omega)
  | fromSrc _ => exact Or.inl rfl

theorem SW.gen_outof_seriesR {s₁ s₂ : SW P K} {i : ℕ} {y : PNode}
    (h : SW.Gen (SW.series s₁ s₂) (.inst i) y) (hi : s₁.nLeaves ≤ i) :
    y = .sink ∨ ∃ j, y = .inst j ∧ s₁.nLeaves ≤ j ∧
      SW.SGen s₂ (i - s₁.nLeaves) (j - s₁.nLeaves) := by
  cases h with
  | struct hs =>
      cases hs with
      | seriesCross h₁ h₂ => exact absurd hi (by omega)
      | @seriesLeft _ _ i' j' h => exact absurd hi (by have := h.bounds; omega)
      | @seriesRight _ _ i' j' h =>
          refine Or.inr ⟨_, rfl, by omega, ?_⟩
          have e₁ : s₁.nLeaves + i' - s₁.nLeaves = i' := by omega
          have e₂ : s₁.nLeaves + j' - s₁.nLeaves = j' := by omega
          rw [e₁, e₂]
          exact h
  | toSink _ => exact Or.inl rfl

theorem SW.gen_into_parL {m : Mode} (hm : m ≠ Mode.seq21) {s₁ s₂ : SW P K}
    {x : PNode} {j : ℕ}
    (h : SW.Gen (SW.par m s₁ s₂) x (.inst j)) (hj : j < s₁.nLeaves) :
    x = .src ∨ ∃ i, x = .inst i ∧ i < s₁.nLeaves ∧ SW.SGen s₁ i j := by
  cases h with
  | struct hs =>
      cases hs with
      | parCross12 h₁ h₂ => exact absurd hj (by omega)
      | parCross21 h₁ h₂ => exact absurd rfl hm
      | parLeft h => exact Or.inr ⟨_, rfl, h.bounds.1, h⟩
      | parRight h => exact absurd hj (by omega)
  | fromSrc _ => exact Or.inl rfl

theorem SW.gen_outof_parL21 {s₁ s₂ : SW P K} {i : ℕ} {y : PNode}
    (h : SW.Gen (SW.par .seq21 s₁ s₂) (.inst i) y) (hi : i < s₁.nLeaves) :
    y = .sink ∨ ∃ j, y = .inst j ∧ j < s₁.nLeaves ∧ SW.SGen s₁ i j := by
  cases h with
  | struct hs =>
      cases hs with
      | parCross21 h₁ h₂ => exact absurd hi (by omega)
      | parLeft h => exact Or.inr ⟨_, rfl, h.bounds.2, h⟩
      | @parRight _ _ _ i' j' h => exact absurd hi (by omega)
  | toSink _ => exact Or.inl rfl

theorem SW.gen_into_parR21 {s₁ s₂ : SW P K} {x : PNode} {j : ℕ}
    (h : SW.Gen (SW.par .seq21 s₁ s₂) x (.inst j)) (hj : s₁.nLeaves ≤ j) :
    x = .src ∨ ∃ i, x = .inst i ∧ s₁.nLeaves ≤ i ∧
      SW.SGen s₂ (i - s₁.nLeaves) (j - s₁.nLeaves) := by
  cases h with
  | struct hs =>
      cases hs with
      | parCross21 h₁ h₂ => exact absurd hj (by omega)
      | @parLeft _ _ _ i' j' h => exact absurd hj (by have := h.bounds; omega)
      | @parRight _ _ _ i' j' h =>
          refine Or.inr ⟨_, rfl, by omega, ?_⟩
          have e₁ : s₁.nLeaves + i' - s₁.nLeaves = i' := by omega
          have e₂ : s₁.nLeaves + j' - s₁.nLeaves = j' := by omega
          rw [e₁, e₂]
          exact h
  | fromSrc _ => exact Or.inl rfl

theorem SW.gen_outof_parR {m : Mode} (hm : m ≠ Mode.seq21) {s₁ s₂ : SW P K}
    {i : ℕ} {y : PNode}
    (h : SW.Gen (SW.par m s₁ s₂) (.inst i) y) (hi : s₁.nLeaves ≤ i) :
    y = .sink ∨ ∃ j, y = .inst j ∧ s₁.nLeaves ≤ j ∧
      SW.SGen s₂ (i - s₁.nLeaves) (j - s₁.nLeaves) := by
  cases h with
  | struct hs =>
      cases hs with
      | parCross12 h₁ h₂ => exact absurd hi (by omega)
      | parCross21 h₁ h₂ => exact absurd rfl hm
      | @parLeft _ _ _ i' j' h => exact absurd hi (by have := h.bounds; omega)
      | @parRight _ _ _ i' j' h =>
          refine Or.inr ⟨_, rfl, by omega, ?_⟩
          have e₁ : s₁.nLeaves + i' - s₁.nLeaves = i' := by omega
          have e₂ : s₁.nLeaves + j' - s₁.nLeaves = j' := by omega
          rw [e₁, e₂]
          exact h
  | toSink _ => exact Or.inl rfl

/-! Descent of ≺ into one arm of a context node, for both endpoints in that
arm.  (Each case uses whichever flavor is confined for that constructor and
mode: e.g. into-left for Series — cross generators only leave the left arm —
and out-of-left for a `seq(2,1)` Par, whose cross generators only enter it.) -/

theorem SW.prec_descend_seriesL {s₁ s₂ : SW P K} {i j : ℕ}
    (h : (SW.series s₁ s₂).Prec (.inst i) (.inst j)) (hj : j < s₁.nLeaves) :
    s₁.Prec (.inst i) (.inst j) := by
  rcases SW.prec_descend_pred (fun _ _ hg hj => SW.gen_into_seriesL hg hj)
      h j rfl hj with h' | ⟨i', heq, _, htr⟩
  · cases h'
  · cases heq
    exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr

theorem SW.prec_descend_seriesR {s₁ s₂ : SW P K} {i j : ℕ}
    (h : (SW.series s₁ s₂).Prec (.inst i) (.inst j)) (hi : s₁.nLeaves ≤ i) :
    s₂.Prec (.inst (i - s₁.nLeaves)) (.inst (j - s₁.nLeaves)) := by
  rcases SW.prec_descend_succ (fun _ _ hg hi => SW.gen_outof_seriesR hg hi)
      h i rfl hi with h' | ⟨j', heq, _, htr⟩
  · cases h'
  · cases heq
    exact SW.transGen_map_prec (f := (· - s₁.nLeaves)) (fun _ _ h => h) htr

theorem SW.prec_descend_parL {m : Mode} {s₁ s₂ : SW P K} {i j : ℕ}
    (h : (SW.par m s₁ s₂).Prec (.inst i) (.inst j))
    (hi : i < s₁.nLeaves) (hj : j < s₁.nLeaves) :
    s₁.Prec (.inst i) (.inst j) := by
  cases m with
  | seq21 =>
      rcases SW.prec_descend_succ (fun _ _ hg hi => SW.gen_outof_parL21 hg hi)
          h i rfl hi with h' | ⟨j', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr
  | conc =>
      rcases SW.prec_descend_pred
          (fun _ _ hg hj => SW.gen_into_parL (by decide) hg hj)
          h j rfl hj with h' | ⟨i', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr
  | seq12 =>
      rcases SW.prec_descend_pred
          (fun _ _ hg hj => SW.gen_into_parL (by decide) hg hj)
          h j rfl hj with h' | ⟨i', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr

theorem SW.prec_descend_parR {m : Mode} {s₁ s₂ : SW P K} {i j : ℕ}
    (h : (SW.par m s₁ s₂).Prec (.inst i) (.inst j))
    (hi : s₁.nLeaves ≤ i) (hj : s₁.nLeaves ≤ j) :
    s₂.Prec (.inst (i - s₁.nLeaves)) (.inst (j - s₁.nLeaves)) := by
  cases m with
  | seq21 =>
      rcases SW.prec_descend_pred (fun _ _ hg hj => SW.gen_into_parR21 hg hj)
          h j rfl hj with h' | ⟨i', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := (· - s₁.nLeaves)) (fun _ _ h => h) htr
  | conc =>
      rcases SW.prec_descend_succ
          (fun _ _ hg hi => SW.gen_outof_parR (by decide) hg hi)
          h i rfl hi with h' | ⟨j', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := (· - s₁.nLeaves)) (fun _ _ h => h) htr
  | seq12 =>
      rcases SW.prec_descend_succ
          (fun _ _ hg hi => SW.gen_outof_parR (by decide) hg hi)
          h i rfl hi with h' | ⟨j', heq, _, htr⟩
      · cases h'
      · cases heq
        exact SW.transGen_map_prec (f := (· - s₁.nLeaves)) (fun _ _ h => h) htr

/-- A designated concurrent Par occurrence inside the SP tree, by its
instance-index block: the left branch occupies `[lo, mid)`, the right branch
`[mid, hi)`. -/
inductive SW.ConcBlock : SW P K → ℕ → ℕ → ℕ → Prop where
  | here {s₁ s₂ : SW P K} :
      SW.ConcBlock (.par .conc s₁ s₂) 0 s₁.nLeaves (s₁.nLeaves + s₂.nLeaves)
  | seriesL {s₁ s₂ : SW P K} {lo mid hi : ℕ} :
      SW.ConcBlock s₁ lo mid hi → SW.ConcBlock (.series s₁ s₂) lo mid hi
  | seriesR {s₁ s₂ : SW P K} {lo mid hi : ℕ} :
      SW.ConcBlock s₂ lo mid hi →
      SW.ConcBlock (.series s₁ s₂)
        (s₁.nLeaves + lo) (s₁.nLeaves + mid) (s₁.nLeaves + hi)
  | parL {m : Mode} {s₁ s₂ : SW P K} {lo mid hi : ℕ} :
      SW.ConcBlock s₁ lo mid hi → SW.ConcBlock (.par m s₁ s₂) lo mid hi
  | parR {m : Mode} {s₁ s₂ : SW P K} {lo mid hi : ℕ} :
      SW.ConcBlock s₂ lo mid hi →
      SW.ConcBlock (.par m s₁ s₂)
        (s₁.nLeaves + lo) (s₁.nLeaves + mid) (s₁.nLeaves + hi)

theorem SW.ConcBlock.le_bounds {s : SW P K} {lo mid hi : ℕ}
    (h : SW.ConcBlock s lo mid hi) : lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ s.nLeaves := by
  induction h with
  | @here s₁ s₂ => rw [SW.nLeaves_par]; omega
  | @seriesL s₁ s₂ lo mid hi h ih => rw [SW.nLeaves_series]; omega
  | @seriesR s₁ s₂ lo mid hi h ih => rw [SW.nLeaves_series]; omega
  | @parL m s₁ s₂ lo mid hi h ih => rw [SW.nLeaves_par]; omega
  | @parR m s₁ s₂ lo mid hi h ih => rw [SW.nLeaves_par]; omega

/-- **Contextual incomparability**: instances on opposite branches of a
concurrent Par are ≺-incomparable *wherever the Par sits in the schedule* —
context generators order nodes relative to the whole Par block, so a cross
path would place some node both before and after the block. -/
theorem SW.ConcBlock.not_cross_prec {s : SW P K} {lo mid hi : ℕ}
    (hb : SW.ConcBlock s lo mid hi) :
    ∀ {i j : ℕ}, lo ≤ i → i < mid → mid ≤ j → j < hi →
      ¬ s.Prec (.inst i) (.inst j) ∧ ¬ s.Prec (.inst j) (.inst i) := by
  induction hb with
  | @here s₁ s₂ =>
      intro i j h1 h2 h3 h4
      constructor
      · intro hp
        have := SW.conc_prec_side hp i j rfl rfl
        omega
      · intro hp
        have := SW.conc_prec_side hp j i rfl rfl
        omega
  | @seriesL s₁ s₂ lo mid hi hcb ih =>
      intro i j h1 h2 h3 h4
      obtain ⟨hlm, hmh, hhn⟩ := hcb.le_bounds
      constructor
      · intro hp
        exact (ih h1 h2 h3 h4).1 (SW.prec_descend_seriesL hp (by omega))
      · intro hp
        exact (ih h1 h2 h3 h4).2 (SW.prec_descend_seriesL hp (by omega))
  | @seriesR s₁ s₂ lo mid hi hcb ih =>
      intro i j h1 h2 h3 h4
      constructor
      · intro hp
        have hd := SW.prec_descend_seriesR hp (by omega)
        have := (ih (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
          (by omega) (by omega) (by omega) (by omega)).1
        exact this hd
      · intro hp
        have hd := SW.prec_descend_seriesR hp (by omega)
        have := (ih (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
          (by omega) (by omega) (by omega) (by omega)).2
        exact this hd
  | @parL m s₁ s₂ lo mid hi hcb ih =>
      intro i j h1 h2 h3 h4
      obtain ⟨hlm, hmh, hhn⟩ := hcb.le_bounds
      constructor
      · intro hp
        exact (ih h1 h2 h3 h4).1
          (SW.prec_descend_parL hp (by omega) (by omega))
      · intro hp
        exact (ih h1 h2 h3 h4).2
          (SW.prec_descend_parL hp (by omega) (by omega))
  | @parR m s₁ s₂ lo mid hi hcb ih =>
      intro i j h1 h2 h3 h4
      constructor
      · intro hp
        have hd := SW.prec_descend_parR hp (by omega) (by omega)
        have := (ih (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
          (by omega) (by omega) (by omega) (by omega)).1
        exact this hd
      · intro hp
        have hd := SW.prec_descend_parR hp (by omega) (by omega)
        have := (ih (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
          (by omega) (by omega) (by omega) (by omega)).2
        exact this hd

/-- An instance user of an allocation either *is* its producer (same
instance, by D7 uniqueness) or strictly follows it (D9). -/
theorem SWF.producer_eq_or_prec {s : SW P K} (hs : SWF s) {a : Alloc P K}
    {i : ℕ} {m : PNode} (hu : IsUser s a (.inst i)) (hm : IsProducer s a m) :
    m = .inst i ∨ s.Prec m (.inst i) := by
  rcases hu with hp | ⟨i', heq, hc⟩ | ⟨heq, _⟩
  · cases a with
    | param p =>
        simp [IsProducer] at hp
    | prod k =>
        simp only [IsProducer] at hp hm
        obtain ⟨i₀, heq₀, hmm⟩ := hp
        obtain ⟨i₁, rfl, hm₁⟩ := hm
        cases heq₀
        exact Or.inl (congrArg PNode.inst (hs.mintsAt_unique hm₁ hmm))
  · cases heq
    exact Or.inr (hs.producer_prec_consumer hc hm)
  · cases heq

/-- **D14 (concurrent Par, contextual)**: for a concurrent Par *anywhere* in
the schedule, two allocations with users on opposite branches always
conflict — neither can be wholly finished before the other's producer,
because that would require an order across the concurrent Par.  This covers
allocations injected into a branch by an enclosing Series (the user is a
consumer) as well as branch-local fresh allocations (the user is the
producer); `SWF.conc_mayOverlap_fresh` is the root-level fresh/fresh special
case. -/
theorem SWF.conc_mayOverlap_of_cross_users {s : SW P K} (hs : SWF s)
    {lo mid hi : ℕ} (hb : SW.ConcBlock s lo mid hi)
    {a b : Alloc P K} {i j : ℕ}
    (hua : IsUser s a (.inst i)) (hi₁ : lo ≤ i) (hi₂ : i < mid)
    (hub : IsUser s b (.inst j)) (hj₁ : mid ≤ j) (hj₂ : j < hi)
    (hab : a ∈ s.forget.buffers) (hbb : b ∈ s.forget.buffers) :
    MayOverlap s a b := by
  obtain ⟨ma, hma⟩ := hs.exists_producer hab
  obtain ⟨mb, hmb⟩ := hs.exists_producer hbb
  have hcross := hb.not_cross_prec hi₁ hi₂ hj₁ hj₂
  constructor
  · intro hall
    have h1 : s.Prec (.inst i) mb := hall _ hua _ hmb
    rcases hs.producer_eq_or_prec hub hmb with rfl | h2
    · exact hcross.1 h1
    · exact hcross.1 (h1.trans h2)
  · intro hall
    have h1 : s.Prec (.inst j) ma := hall _ hub _ hma
    rcases hs.producer_eq_or_prec hua hma with rfl | h2
    · exact hcross.2 h1
    · exact hcross.2 (h1.trans h2)

end WorkGraph
