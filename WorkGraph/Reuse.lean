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

* **Sequentialized-Par reuse** (`SWF.par12_not_mayOverlap_internal_fresh`):
  the same for `Par` in mode `seq(1,2)` (the `seq(2,1)` case is the mirror
  image).

* **No concurrent cross-branch reuse** (`SWF.conc_mayOverlap_fresh`): in a
  concurrent Par, fresh allocations of opposite branches always conflict —
  no order exists between the branches (`SW.conc_prec_side`: ≺ never crosses
  a concurrent Par).
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

end WorkGraph
