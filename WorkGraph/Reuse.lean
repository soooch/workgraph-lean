/-
# Work Graph Model — Stage 5: Reuse legality (D14, with D6-forward en route)

Proves the memory-reuse payoff of the model (D14) through one generic
lemma:

* **Sequential blocks** (`SW.SeqBlock`): a designated Series or
  sequentialized-Par occurrence anywhere in the schedule, by the index
  blocks of its earlier and later arms; every earlier-block instance
  structurally precedes every later-block instance
  (`SeqBlock.cross_sgen` — D13's over-ordering of dead ends included).

* **Generic confined-users reuse** (`not_conflict_of_confined`): users of
  `a` confined to the earlier block + producers of `b` in the later block
  ⟹ no conflict.  The three sequential D14 theorems
  (`SWF.series_not_conflict_internal_fresh`,
  `SWF.par12_not_conflict_internal_fresh`,
  `SWF.par21_not_conflict_internal_fresh`) are instantiations, via the
  D6-forward confinement lemmas (`users_confined_seriesL/parL/parR`) and
  producer localization; and the contextual versions follow the same way —
  `SWF.series_reuse_in_conc_context` walks a `Par_conc(Series(W₁,W₂), V)`
  context as the acceptance case.

* **No concurrent cross-branch reuse**: no order crosses a concurrent Par —
  at the root (`SW.conc_prec_side`) and, contextually, for a concurrent Par
  anywhere inside a larger composite (`SW.ConcBlock.not_cross_prec`, via
  block-descent of ≺-paths).  Hence fresh allocations of opposite branches
  always conflict at the root (`SWF.conc_conflict_fresh`), and in general
  *any* two allocations with users on opposite branches of any concurrent
  Par conflict (`SWF.conc_conflict_of_cross_users`) — covering allocations
  injected into a branch by an enclosing Series.
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

/-! ## D14: sequential blocks and the generic confined-users reuse lemma

A `SeqBlock` designates an *ordered* pair of arm blocks anywhere in the
schedule: a Series, or a sequentialized Par, whose **earlier** arm occupies
the instance-index block `[elo, ehi)` and **later** arm `[llo, lhi)` (for
`seq(2,1)` the earlier arm is the *right* arm, so the earlier block is the
higher index range).  Every earlier-block instance structurally precedes
every later-block instance (`SeqBlock.cross_sgen`), so reuse legality for
all three sequential composites — at the root or in any context — is one
lemma, `not_conflict_of_confined`, instantiated with confinement facts. -/

/-- A designated Series / sequentialized-Par occurrence, by the index blocks
of its earlier arm `[elo, ehi)` and later arm `[llo, lhi)`. -/
inductive SW.SeqBlock : SW P K → ℕ → ℕ → ℕ → ℕ → Prop where
  | series {s₁ s₂ : SW P K} :
      SW.SeqBlock (.series s₁ s₂) 0 s₁.nLeaves
        s₁.nLeaves (s₁.nLeaves + s₂.nLeaves)
  | par12 {s₁ s₂ : SW P K} :
      SW.SeqBlock (.par .seq12 s₁ s₂) 0 s₁.nLeaves
        s₁.nLeaves (s₁.nLeaves + s₂.nLeaves)
  | par21 {s₁ s₂ : SW P K} :
      SW.SeqBlock (.par .seq21 s₁ s₂) s₁.nLeaves (s₁.nLeaves + s₂.nLeaves)
        0 s₁.nLeaves
  | seriesL {s₁ s₂ : SW P K} {elo ehi llo lhi : ℕ} :
      SW.SeqBlock s₁ elo ehi llo lhi →
      SW.SeqBlock (.series s₁ s₂) elo ehi llo lhi
  | seriesR {s₁ s₂ : SW P K} {elo ehi llo lhi : ℕ} :
      SW.SeqBlock s₂ elo ehi llo lhi →
      SW.SeqBlock (.series s₁ s₂) (s₁.nLeaves + elo) (s₁.nLeaves + ehi)
        (s₁.nLeaves + llo) (s₁.nLeaves + lhi)
  | parL {m : Mode} {s₁ s₂ : SW P K} {elo ehi llo lhi : ℕ} :
      SW.SeqBlock s₁ elo ehi llo lhi →
      SW.SeqBlock (.par m s₁ s₂) elo ehi llo lhi
  | parR {m : Mode} {s₁ s₂ : SW P K} {elo ehi llo lhi : ℕ} :
      SW.SeqBlock s₂ elo ehi llo lhi →
      SW.SeqBlock (.par m s₁ s₂) (s₁.nLeaves + elo) (s₁.nLeaves + ehi)
        (s₁.nLeaves + llo) (s₁.nLeaves + lhi)

/-- Every earlier-block instance structurally precedes every later-block
instance — the 4.3 clause of the designated Series/seq-Par, lifted through
the context (this is also D13's load-bearing over-ordering: dead ends of the
earlier arm are ordered too). -/
theorem SW.SeqBlock.cross_sgen {s : SW P K} {elo ehi llo lhi : ℕ}
    (hb : SW.SeqBlock s elo ehi llo lhi) :
    ∀ {i j : ℕ}, elo ≤ i → i < ehi → llo ≤ j → j < lhi → SW.SGen s i j := by
  induction hb with
  | @series s₁ s₂ =>
      intro i j hi₁ hi₂ hj₁ hj₂
      have h := SW.SGen.seriesCross (s₁ := s₁) (s₂ := s₂) (i := i)
        (j := j - s₁.nLeaves) hi₂ (by omega)
      have e : s₁.nLeaves + (j - s₁.nLeaves) = j := by omega
      rwa [e] at h
  | @par12 s₁ s₂ =>
      intro i j hi₁ hi₂ hj₁ hj₂
      have h := SW.SGen.parCross12 (s₁ := s₁) (s₂ := s₂) (i := i)
        (j := j - s₁.nLeaves) hi₂ (by omega)
      have e : s₁.nLeaves + (j - s₁.nLeaves) = j := by omega
      rwa [e] at h
  | @par21 s₁ s₂ =>
      intro i j hi₁ hi₂ hj₁ hj₂
      have h := SW.SGen.parCross21 (s₁ := s₁) (s₂ := s₂)
        (i := i - s₁.nLeaves) (j := j) (by omega) hj₂
      have e : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
      rwa [e] at h
  | seriesL hb ih =>
      intro i j hi₁ hi₂ hj₁ hj₂
      exact .seriesLeft (ih hi₁ hi₂ hj₁ hj₂)
  | @seriesR s₁ s₂ elo ehi llo lhi hb ih =>
      intro i j hi₁ hi₂ hj₁ hj₂
      have h := SW.SGen.seriesRight (s₁ := s₁) (s₂ := s₂)
        (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
        (ih (by omega) (by omega) (by omega) (by omega))
      have e₁ : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
      have e₂ : s₁.nLeaves + (j - s₁.nLeaves) = j := by omega
      rwa [e₁, e₂] at h
  | parL hb ih =>
      intro i j hi₁ hi₂ hj₁ hj₂
      exact .parLeft (ih hi₁ hi₂ hj₁ hj₂)
  | @parR m s₁ s₂ elo ehi llo lhi hb ih =>
      intro i j hi₁ hi₂ hj₁ hj₂
      have h := SW.SGen.parRight (m := m) (s₁ := s₁) (s₂ := s₂)
        (i := i - s₁.nLeaves) (j := j - s₁.nLeaves)
        (ih (by omega) (by omega) (by omega) (by omega))
      have e₁ : s₁.nLeaves + (i - s₁.nLeaves) = i := by omega
      have e₂ : s₁.nLeaves + (j - s₁.nLeaves) = j := by omega
      rwa [e₁, e₂] at h

/-- **Generic sequential reuse** (D14, unfolding 4.4/4.5): if every user of
`a` lies in the earlier block of a `SeqBlock` and every producer of `b` in
its later block, then `a` is finished before `b`'s producer starts — no
conflict, root-level or in context. -/
theorem not_conflict_of_confined {s : SW P K}
    {elo ehi llo lhi : ℕ} (hb : SW.SeqBlock s elo ehi llo lhi)
    {a b : Alloc P K}
    (husers : ∀ n, IsUser s a n → ∃ i, n = .inst i ∧ elo ≤ i ∧ i < ehi)
    (hprod : ∀ m, IsProducer s b m → ∃ j, m = .inst j ∧ llo ≤ j ∧ j < lhi) :
    ¬ Conflict s a b := fun hov =>
  hov.1 fun n hn m hm => by
    obtain ⟨i, rfl, hi₁, hi₂⟩ := husers n hn
    obtain ⟨j, rfl, hj₁, hj₂⟩ := hprod m hm
    exact Relation.TransGen.single (SW.Gen.struct (hb.cross_sgen hi₁ hi₂ hj₁ hj₂))

/-! ### Confinement and localization facts (D6, forward direction) -/

/-- Producers of an ID minted in the right arm are right-block instances. -/
theorem producer_localized_right {s t₁ t₂ : SW P K}
    (hsl : s.leaves = t₁.leaves ++ t₂.leaves)
    (hd : MintDisjoint t₁.forget t₂.forget) {k : K}
    (hk : k ∈ t₂.forget.minted) :
    ∀ m, IsProducer s (.prod k) m →
      ∃ j, m = .inst j ∧ t₁.nLeaves ≤ j ∧ j < t₁.nLeaves + t₂.nLeaves := by
  intro m hm
  simp only [IsProducer] at hm
  obtain ⟨j, rfl, hm⟩ := hm
  obtain ⟨hge, hm₂⟩ := hm.resolve_right hsl hd hk
  exact ⟨j, rfl, hge, by have := hm₂.lt_nLeaves; omega⟩

/-- Producers of an ID minted in the left arm are left-block instances. -/
theorem producer_localized_left {s t₁ t₂ : SW P K}
    (hsl : s.leaves = t₁.leaves ++ t₂.leaves)
    (hd : MintDisjoint t₁.forget t₂.forget) {k : K}
    (hk : k ∈ t₁.forget.minted) :
    ∀ m, IsProducer s (.prod k) m → ∃ j, m = .inst j ∧ j < t₁.nLeaves := by
  intro m hm
  simp only [IsProducer] at hm
  obtain ⟨j, rfl, hm⟩ := hm
  exact ⟨j, rfl, (hm.resolve_left hsl hd hk).1⟩

/-- **D6 (forward), Series**: every user of a left-internal allocation of a
series composite is a left-arm instance — the producer by D4 + mint
disjointness, consumers because a right-arm binding is either a right-minted
ID (excluded by distinctness) or θ-rewritten into `outputs(W₁)` (excluded by
internality), and τ because internality survives into the composite (D5). -/
theorem SWF.users_confined_seriesL {s₁ s₂ : SW P K} {θ : Subst P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂) (hθ : ThetaFits θ s₁.forget s₂.forget)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal) :
    ∀ n, IsUser (SW.series s₁ (s₂.rebind θ)) a n →
      ∃ i, n = .inst i ∧ i < s₁.nLeaves := by
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  have hpd : θ.ParamDom := hθ.paramDom hwf₂
  obtain ⟨hbuf, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₁.param_mem_inputs_of_mem_buffers p hbuf) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₁ : k' ∈ s₁.forget.minted :=
    hwf₁.mem_minted_of_prod_mem_buffers k' hbuf
  have hint : Alloc.prod k' ∈ (SW.series s₁ (s₂.rebind θ)).forget.internal := by
    have hforget : (SW.series s₁ (s₂.rebind θ)).forget =
        s₁.forget.mkSeries s₂.forget θ := by
      simp [W.mkSeries]
    rw [hforget, hwf₁.internal_mkSeries hwf₂ hθ hd]
    exact Or.inl (Or.inl ⟨hbuf, hni, hno⟩)
  rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
  · simp only [IsProducer] at hp
    obtain ⟨i₀, rfl, hm⟩ := hp
    exact ⟨i₀, rfl, (hm.resolve_left rfl (hd.rebind_right θ) hk'₁).1⟩
  · refine ⟨i, rfl, ?_⟩
    rcases consumesAt_series_iff.mp hc with ⟨hi, -⟩ | ⟨-, hc'⟩
    · exact hi
    · exfalso
      obtain ⟨b₀, hc₂, hab⟩ := consumesAt_rebind_iff.mp hc'
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
  · exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)

/-- **D6 (forward), Par (left)**: every user of a left-internal allocation
of a Par composite — in any mode — is a left-branch instance. -/
theorem SWF.users_confined_parL {m : Mode} {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂) (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal) :
    ∀ n, IsUser (SW.par m s₁ s₂) a n → ∃ i, n = .inst i ∧ i < s₁.nLeaves := by
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  obtain ⟨hbuf, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₁.param_mem_inputs_of_mem_buffers p hbuf) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₁ : k' ∈ s₁.forget.minted :=
    hwf₁.mem_minted_of_prod_mem_buffers k' hbuf
  have hint : Alloc.prod k' ∈ (SW.par m s₁ s₂).forget.internal := by
    have he : (SW.par m s₁ s₂).forget = W.par s₁.forget s₂.forget := rfl
    rw [he, hwf₁.internal_par hwf₂ hd]
    exact Or.inl ⟨hbuf, hni, hno⟩
  rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
  · simp only [IsProducer] at hp
    obtain ⟨i₀, rfl, hm⟩ := hp
    exact ⟨i₀, rfl, (hm.resolve_left rfl hd hk'₁).1⟩
  · refine ⟨i, rfl, ?_⟩
    rcases consumesAt_par_iff.mp hc with ⟨hi, -⟩ | ⟨-, hc₂⟩
    · exact hi
    · exact (hd k' hk'₁
        (hwf₂.mem_minted_of_prod_mem_buffers k' hc₂.mem_buffers)).elim
  · exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)

/-- **D6 (forward), Par (right)**: every user of a right-internal allocation
of a Par composite — in any mode — is a right-branch instance. -/
theorem SWF.users_confined_parR {m : Mode} {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂) (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₂.forget.internal) :
    ∀ n, IsUser (SW.par m s₁ s₂) a n →
      ∃ i, n = .inst i ∧ s₁.nLeaves ≤ i ∧ i < s₁.nLeaves + s₂.nLeaves := by
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  obtain ⟨hbuf, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₂.param_mem_inputs_of_mem_buffers p hbuf) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₂ : k' ∈ s₂.forget.minted :=
    hwf₂.mem_minted_of_prod_mem_buffers k' hbuf
  have hint : Alloc.prod k' ∈ (SW.par m s₁ s₂).forget.internal := by
    have he : (SW.par m s₁ s₂).forget = W.par s₁.forget s₂.forget := rfl
    rw [he, hwf₁.internal_par hwf₂ hd]
    exact Or.inr ⟨hbuf, hni, hno⟩
  rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
  · simp only [IsProducer] at hp
    obtain ⟨i₀, rfl, hm⟩ := hp
    obtain ⟨hge, hm₂⟩ := hm.resolve_right rfl hd hk'₂
    exact ⟨i₀, rfl, hge, by have := hm₂.lt_nLeaves; omega⟩
  · rcases consumesAt_par_iff.mp hc with ⟨-, hc₁⟩ | ⟨hge, hc₂⟩
    · exact (hd k'
        (hwf₁.mem_minted_of_prod_mem_buffers k' hc₁.mem_buffers) hk'₂).elim
    · exact ⟨i, rfl, hge, by have := hc₂.lt_nLeaves; omega⟩
  · exact absurd hif (fun hif => hif.elim hint.2.1 hint.2.2)

/-! ### The three sequential D14 theorems, as instantiations -/

/-- **D14 (Series)**: `a ∈ internal(W₁)` never conflicts with a fresh
allocation of the right arm — `internal(W₁)` is fully reusable past the
Series boundary. -/
theorem SWF.series_not_conflict_internal_fresh {s₁ s₂ : SW P K}
    {θ : Subst P K} (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hθ : ThetaFits θ s₁.forget s₂.forget)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal)
    {k : K} (hk : k ∈ s₂.forget.minted) :
    ¬ Conflict (SW.series s₁ (s₂.rebind θ)) a (.prod k) := by
  refine not_conflict_of_confined SW.SeqBlock.series ?_ ?_
  · intro n hn
    obtain ⟨i, rfl, hi⟩ := SWF.users_confined_seriesL h₁ h₂ hθ hd ha n hn
    exact ⟨i, rfl, Nat.zero_le _, hi⟩
  · exact producer_localized_right rfl (hd.rebind_right θ) (by simpa using hk)

/-- **D14 (sequentialized Par, `seq(1,2)`)**: an internal allocation of the
first branch never conflicts with a fresh allocation of the second —
internal buffers of the earlier branch are reusable by the later one. -/
theorem SWF.par12_not_conflict_internal_fresh {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal)
    {k : K} (hk : k ∈ s₂.forget.minted) :
    ¬ Conflict (SW.par .seq12 s₁ s₂) a (.prod k) := by
  refine not_conflict_of_confined SW.SeqBlock.par12 ?_ ?_
  · intro n hn
    obtain ⟨i, rfl, hi⟩ := SWF.users_confined_parL h₁ h₂ hd ha n hn
    exact ⟨i, rfl, Nat.zero_le _, hi⟩
  · exact producer_localized_right rfl hd hk

/-- **D14 (sequentialized Par, `seq(2,1)`)**: the mirror — an internal
allocation of the *second* branch (which `seq(2,1)` runs first) never
conflicts with a fresh allocation of the first. -/
theorem SWF.par21_not_conflict_internal_fresh {s₁ s₂ : SW P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂)
    (hd : MintDisjoint s₁.forget s₂.forget)
    {a : Alloc P K} (ha : a ∈ s₂.forget.internal)
    {k : K} (hk : k ∈ s₁.forget.minted) :
    ¬ Conflict (SW.par .seq21 s₁ s₂) a (.prod k) := by
  refine not_conflict_of_confined SW.SeqBlock.par21 ?_ ?_
  · exact SWF.users_confined_parR h₁ h₂ hd ha
  · intro m hm
    obtain ⟨j, rfl, hj⟩ := producer_localized_left rfl hd hk m hm
    exact ⟨j, rfl, Nat.zero_le _, hj⟩

/-! ### Contextual acceptance: sequential reuse inside a larger composite -/

/-- **D14, contextual (acceptance test)**: inside
`Par_conc(Series(W₁, W₂), V)`, the internal allocations of `W₁` are still
reusable by `W₂`'s fresh allocations — the confinement and localization
facts walk the enclosing context, and the `SeqBlock` context constructors
carry the ordering. -/
theorem SWF.series_reuse_in_conc_context {s₁ s₂ v : SW P K} {θ : Subst P K}
    (h₁ : SWF s₁) (h₂ : SWF s₂) (hθ : ThetaFits θ s₁.forget s₂.forget)
    (hd : MintDisjoint s₁.forget s₂.forget) (hv : SWF v)
    (hdv : MintDisjoint (SW.series s₁ (s₂.rebind θ)).forget v.forget)
    {a : Alloc P K} (ha : a ∈ s₁.forget.internal)
    {k : K} (hk : k ∈ s₂.forget.minted) :
    ¬ Conflict (SW.par .conc (SW.series s₁ (s₂.rebind θ)) v) a (.prod k) := by
  have hwf₁ := h₁.forget_wf
  have hwf₂ := h₂.forget_wf
  have hwfv := hv.forget_wf
  have htwf : SWF (SW.series s₁ (s₂.rebind θ)) := SWF.series h₁ h₂ hθ hd
  -- a is a produced ID minted in W₁, internal to the series composite
  obtain ⟨hbuf, hni, hno⟩ := ha
  obtain ⟨k', rfl⟩ : ∃ k', a = Alloc.prod k' := by
    cases a with
    | param p => exact absurd (hwf₁.param_mem_inputs_of_mem_buffers p hbuf) hni
    | prod k' => exact ⟨k', rfl⟩
  have hk'₁ : k' ∈ s₁.forget.minted :=
    hwf₁.mem_minted_of_prod_mem_buffers k' hbuf
  have hk't : k' ∈ (SW.series s₁ (s₂.rebind θ)).forget.minted := Or.inl hk'₁
  have hkt : k ∈ (SW.series s₁ (s₂.rebind θ)).forget.minted :=
    Or.inr (by simpa using hk)
  have hint : Alloc.prod k' ∈ (SW.series s₁ (s₂.rebind θ)).forget.internal := by
    have hforget : (SW.series s₁ (s₂.rebind θ)).forget =
        s₁.forget.mkSeries s₂.forget θ := by
      simp [W.mkSeries]
    rw [hforget, hwf₁.internal_mkSeries hwf₂ hθ hd]
    exact Or.inl (Or.inl ⟨hbuf, hni, hno⟩)
  refine not_conflict_of_confined (SW.SeqBlock.parL SW.SeqBlock.series) ?_ ?_
  · -- users of a stay in W₁'s block, through the Par context
    rintro n (hp | ⟨i, rfl, hc⟩ | ⟨rfl, hif⟩)
    · simp only [IsProducer] at hp
      obtain ⟨i₀, rfl, hm⟩ := hp
      obtain ⟨hit, hmt⟩ := hm.resolve_left rfl hdv hk't
      exact ⟨i₀, rfl, Nat.zero_le _,
        (hmt.resolve_left rfl (hd.rebind_right θ) hk'₁).1⟩
    · rcases consumesAt_par_iff.mp hc with ⟨hit, hct⟩ | ⟨-, hcv⟩
      · -- consumer inside the series composite: reuse the series confinement
        obtain ⟨i', heq, hi'⟩ := SWF.users_confined_seriesL h₁ h₂ hθ hd
          ⟨hbuf, hni, hno⟩ (.inst i) (Or.inr (Or.inl ⟨i, rfl, hct⟩))
        cases heq
        exact ⟨i, rfl, Nat.zero_le _, hi'⟩
      · -- consumer in V: V cannot reference an ID minted in the series arm
        exact (hdv k' hk't
          (hwfv.mem_minted_of_prod_mem_buffers k' hcv.mem_buffers)).elim
    · -- τ: a is not interface anywhere up the context
      exfalso
      rcases hif with hin | hout
      · rcases hin with hin | hin
        · exact (hwf₁.inputs_isParam _ hin).elim
        · exact (hwfv.inputs_isParam _ hin).elim
      · rcases hout with hout | hout
        · exact hint.2.2 hout
        · exact hdv k' hk't (hwfv.mem_minted_of_prod_mem_buffers k'
            (v.forget.outputs_subset_buffers hout))
  · -- producers of b sit in W₂'s block
    intro m hm
    simp only [IsProducer] at hm
    obtain ⟨j, rfl, hm⟩ := hm
    obtain ⟨hjt, hmt⟩ := hm.resolve_left rfl hdv hkt
    obtain ⟨hge, hm₂⟩ := hmt.resolve_right rfl (hd.rebind_right θ)
      (by simpa using hk)
    exact ⟨j, rfl, hge, by have := hm₂.lt_nLeaves; omega⟩

/-! ## D14: no concurrent cross-branch reuse -/

/-- **D14 (concurrent Par)**: fresh allocations of opposite branches of a
concurrent Par always conflict — no order exists between the branches, so
4.5 keeps them address-disjoint. -/
theorem SWF.conc_conflict_fresh {s₁ s₂ : SW P K}
    (hd : MintDisjoint s₁.forget s₂.forget)
    {k₁ k₂ : K} (hk₁ : k₁ ∈ s₁.forget.minted) (hk₂ : k₂ ∈ s₂.forget.minted) :
    Conflict (SW.par .conc s₁ s₂) (.prod k₁) (.prod k₂) := by
  set s : SW P K := SW.par .conc s₁ s₂ with hs_def
  have hmem₁ : k₁ ∈ s.forget.minted := Or.inl hk₁
  have hmem₂ : k₂ ∈ s.forget.minted := Or.inr hk₂
  obtain ⟨i₁, hm₁⟩ := exists_mintsAt hmem₁
  obtain ⟨i₂, hm₂⟩ := exists_mintsAt hmem₂
  have hside₁ : i₁ < s₁.nLeaves := (hm₁.resolve_left rfl hd hk₁).1
  have hside₂ : s₁.nLeaves ≤ i₂ := (hm₂.resolve_right rfl hd hk₂).1
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
  by_cases hm : m = Mode.seq21
  · subst hm
    rcases SW.prec_descend_succ (fun _ _ hg hi => SW.gen_outof_parL21 hg hi)
        h i rfl hi with h' | ⟨j', heq, _, htr⟩
    · cases h'
    · cases heq
      exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr
  · rcases SW.prec_descend_pred
        (fun _ _ hg hj => SW.gen_into_parL hm hg hj)
        h j rfl hj with h' | ⟨i', heq, _, htr⟩
    · cases h'
    · cases heq
      exact SW.transGen_map_prec (f := id) (fun _ _ h => h) htr

theorem SW.prec_descend_parR {m : Mode} {s₁ s₂ : SW P K} {i j : ℕ}
    (h : (SW.par m s₁ s₂).Prec (.inst i) (.inst j))
    (hi : s₁.nLeaves ≤ i) (hj : s₁.nLeaves ≤ j) :
    s₂.Prec (.inst (i - s₁.nLeaves)) (.inst (j - s₁.nLeaves)) := by
  by_cases hm : m = Mode.seq21
  · subst hm
    rcases SW.prec_descend_pred (fun _ _ hg hj => SW.gen_into_parR21 hg hj)
        h j rfl hj with h' | ⟨i', heq, _, htr⟩
    · cases h'
    · cases heq
      exact SW.transGen_map_prec (f := (· - s₁.nLeaves)) (fun _ _ h => h) htr
  · rcases SW.prec_descend_succ
        (fun _ _ hg hi => SW.gen_outof_parR hm hg hi)
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
producer); `SWF.conc_conflict_fresh` is the root-level fresh/fresh special
case. -/
theorem SWF.conc_conflict_of_cross_users {s : SW P K} (hs : SWF s)
    {lo mid hi : ℕ} (hb : SW.ConcBlock s lo mid hi)
    {a b : Alloc P K} {i j : ℕ}
    (hua : IsUser s a (.inst i)) (hi₁ : lo ≤ i) (hi₂ : i < mid)
    (hub : IsUser s b (.inst j)) (hj₁ : mid ≤ j) (hj₂ : j < hi)
    (hab : a ∈ s.forget.buffers) (hbb : b ∈ s.forget.buffers) :
    Conflict s a b := by
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
