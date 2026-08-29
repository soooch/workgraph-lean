/-
# Work Graph Model — Stage 2: Composition as substitution, well-formedness

Formalizes §2.4 (Series carries a binding substitution) and proves the §5
derived properties about the term calculus:

* **D3** (composition closure): inputs of a well-formed term are parameters
  (`WF.inputs_isParam`); a parameter in `outputs(W)` lies in `inputs(W)`
  (`WF.param_mem_inputs_of_mem_outputs`); every parameter occurring anywhere
  in `W` names a member of `inputs(W)` (`WF.param_mem_inputs_of_mem_buffers`,
  `WF.param_occurs_iff`); the rewritten right arm's inputs land in the left
  arm's outputs (`ThetaFits.inputs_rebind_subset_outputs`).
  (Totality of `bind`/`res` — "bind is total at every stage, so res is" —
  holds by type in this formalization: both are total functions.)

* **D4** (externality): `dom(θ) ⊆ 𝔸_π` (`ThetaFits.paramDom` — so a binding,
  once produced-valued, is never rewritten: `Subst.apply_prod`), and every
  produced ID in `buffers(W)` is minted by a node of `W`
  (`WF.mem_minted_of_prod_mem_buffers`).

* **D5** (unfolded internals): `WF.internal_par` and `WF.internal_mkSeries`.

Representation note: spec `Series(W₁, W₂, θ)` is `W.mkSeries w₁ w₂ θ =
W.series w₁ (w₂.rebind θ)` — the composite stores the rewritten right arm.
The substitution is applied simultaneously and exactly once to the
pre-composition bindings (2.4): `rebind` maps each leaf binding through
`θ.apply` a single time, never iterating.
-/
import WorkGraph.Syntax

namespace WorkGraph

variable {P K : Type*}

/-! ## §2.4 Binding substitutions -/

/-- A binding substitution θ: a partial map on allocation IDs.  `none` means
"not in `dom(θ)`". -/
def Subst (P K : Type*) := Alloc P K → Option (Alloc P K)

namespace Subst

variable (θ : Subst P K)

/-- `bind′` of 2.4: `θ(a)` if `a ∈ dom(θ)`, else `a`. -/
def apply (a : Alloc P K) : Alloc P K := (θ a).getD a

theorem apply_of_none {a : Alloc P K} (h : θ a = none) : θ.apply a = a := by
  simp [apply, h]

theorem apply_of_some {a b : Alloc P K} (h : θ a = some b) : θ.apply a = b := by
  simp [apply, h]

/-- `dom(θ) ⊆ 𝔸_π`: θ never rewrites a produced-valued binding.  Per **D4**
this holds for every legal Series formation (`ThetaFits.paramDom`). -/
def ParamDom : Prop := ∀ k : K, θ (.prod k) = none

theorem ParamDom.apply_prod {θ : Subst P K} (hθ : θ.ParamDom) (k : K) :
    θ.apply (.prod k) = .prod k :=
  θ.apply_of_none (hθ k)

end Subst

/-! ## Rebinding (the substitution step of 2.4) -/

/-- Rewrite one node instance's binding through θ (a single, simultaneous
application — 2.4).  Signature and minted IDs are untouched. -/
def LeafInst.rebind (l : LeafInst P K) (θ : Subst P K) : LeafInst P K :=
  ⟨l.sig, fun j => θ.apply (l.bind j), l.mint⟩

@[simp] theorem LeafInst.sig_rebind (l : LeafInst P K) (θ : Subst P K) :
    (l.rebind θ).sig = l.sig := rfl

@[simp] theorem LeafInst.minted_rebind (l : LeafInst P K) (θ : Subst P K) :
    (l.rebind θ).minted = l.minted := rfl

/-- Rewrite every binding of a term through θ.  Bindings live only at leaves,
so this is the structural map; each binding is rewritten exactly once. -/
def W.rebind (θ : Subst P K) : W P K → W P K
  | .leaf l => .leaf (l.rebind θ)
  | .series w₁ w₂ => .series (rebind θ w₁) (rebind θ w₂)
  | .par w₁ w₂ => .par (rebind θ w₁) (rebind θ w₂)

@[simp] theorem W.minted_rebind (θ : Subst P K) (w : W P K) :
    (w.rebind θ).minted = w.minted := by
  induction w with
  | leaf l => simp [rebind]
  | series w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]
  | par w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]

@[simp] theorem W.leaves_rebind (θ : Subst P K) (w : W P K) :
    (w.rebind θ).leaves = w.leaves.map (·.rebind θ) := by
  induction w with
  | leaf l => simp [rebind]
  | series w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]
  | par w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂]

/-- Resolution commutes with rebinding, provided θ does not touch produced
IDs (which D4 guarantees for legal formations): a fresh slot still resolves
to its minted ID, a passthrough slot to the rewritten binding. -/
theorem LeafInst.resOut_rebind {θ : Subst P K} (hθ : θ.ParamDom)
    (l : LeafInst P K) (k : Fin l.sig.nOut) :
    (l.rebind θ).resOut k = θ.apply (l.resOut k) := by
  rcases h : l.sig.prov k with _ | j
  · have h1 : l.resOut k = .prod (l.mint k) := by unfold resOut; rw [h]
    have h2 : (l.rebind θ).resOut k = .prod (l.mint k) := by
      unfold resOut; rw [show (l.rebind θ).sig.prov k = none from h]; rfl
    rw [h1, h2, hθ.apply_prod]
  · have h1 : l.resOut k = l.bind j := by unfold resOut; rw [h]
    have h2 : (l.rebind θ).resOut k = θ.apply (l.bind j) := by
      unfold resOut; rw [show (l.rebind θ).sig.prov k = some j from h]; rfl
    rw [h1, h2]

theorem LeafInst.inputs_rebind (l : LeafInst P K) (θ : Subst P K) :
    (l.rebind θ).inputs = θ.apply '' l.inputs := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨l.bind j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

theorem LeafInst.outputs_rebind {θ : Subst P K} (hθ : θ.ParamDom)
    (l : LeafInst P K) :
    (l.rebind θ).outputs = θ.apply '' l.outputs := by
  unfold LeafInst.outputs
  rw [show (l.rebind θ).resOut = fun k => θ.apply (l.resOut k) from
        funext (l.resOut_rebind hθ), ← Set.range_comp]
  rfl

/-- ID-set functions of a rewritten term are images of the original's:
"every function of 2.3 reads current bindings" (2.4). -/
theorem W.inputs_rebind (θ : Subst P K) (w : W P K) :
    (w.rebind θ).inputs = θ.apply '' w.inputs := by
  induction w with
  | leaf l => simpa [rebind] using l.inputs_rebind θ
  | series w₁ w₂ ih₁ ih₂ => simpa [rebind] using ih₁
  | par w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂, Set.image_union]

theorem W.outputs_rebind {θ : Subst P K} (hθ : θ.ParamDom) (w : W P K) :
    (w.rebind θ).outputs = θ.apply '' w.outputs := by
  induction w with
  | leaf l => simpa [rebind] using l.outputs_rebind hθ
  | series w₁ w₂ ih₁ ih₂ => simpa [rebind] using ih₂
  | par w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂, Set.image_union]

theorem W.buffers_rebind {θ : Subst P K} (hθ : θ.ParamDom) (w : W P K) :
    (w.rebind θ).buffers = θ.apply '' w.buffers := by
  induction w with
  | leaf l =>
      simp [rebind, l.inputs_rebind θ, l.outputs_rebind hθ, Set.image_union]
  | series w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂, Set.image_union]
  | par w₁ w₂ ih₁ ih₂ => simp [rebind, ih₁, ih₂, Set.image_union]

/-! ## Legal Series formation and well-formed terms -/

/-- 2.4: `θ : inputs(W₂) → outputs(W₁)`, total on `inputs(W₂)` (surjectivity
not required), and defined on nothing else.  Judged against the
pre-composition bindings of `w₂` ("the right arm is standalone at that
moment", D4). -/
structure ThetaFits (θ : Subst P K) (w₁ w₂ : W P K) : Prop where
  dom_eq : ∀ a, (θ a).isSome ↔ a ∈ w₂.inputs
  codom : ∀ a b, θ a = some b → b ∈ w₁.outputs

/-- Spec `Series(W₁, W₂, θ)`: the composite contains the rewritten `W₂`. -/
def W.mkSeries (w₁ w₂ : W P K) (θ : Subst P K) : W P K :=
  .series w₁ (w₂.rebind θ)

/-- 2.1: produced IDs are globally distinct, so two composed terms never
mint a common ID. -/
def MintDisjoint (w₁ w₂ : W P K) : Prop :=
  ∀ k, k ∈ w₁.minted → k ∈ w₂.minted → False

/-- **Well-formed work terms**: exactly the terms arising from the legal
formations of §1.1/§2.2/§2.4 —

* a standalone leaf's binding is parameter-valued (`bind = β : InSlots → 𝔸_π`,
  2.2) and its fresh slots mint distinct IDs (2.1);
* Series formation applies a fitting substitution to the right arm (2.4);
* Par introduces no bindings (2.4);
* across any composition, minted IDs stay globally distinct (2.1). -/
inductive WF : W P K → Prop
  | leaf {l : LeafInst P K} :
      (∀ j, (l.bind j).IsParam) → l.MintInj → WF (.leaf l)
  | series {w₁ w₂ : W P K} {θ : Subst P K} :
      WF w₁ → WF w₂ → ThetaFits θ w₁ w₂ → MintDisjoint w₁ w₂ →
      WF (w₁.mkSeries w₂ θ)
  | par {w₁ w₂ : W P K} :
      WF w₁ → WF w₂ → MintDisjoint w₁ w₂ → WF (.par w₁ w₂)

/-! ## D3 / D4: composition closure and externality -/

/-- **D3** (first part): the inputs of a well-formed term are parameters —
`inputs(W) ⊆ 𝔸_π`.  The inputs of a standalone term are exactly its free
variables. -/
theorem WF.inputs_isParam {w : W P K} (h : WF w) :
    ∀ a ∈ w.inputs, a.IsParam := by
  induction h with
  | leaf hβ _ =>
      rintro a ⟨j, rfl⟩
      exact hβ j
  | series h₁ h₂ hθ hd ih₁ ih₂ =>
      exact ih₁
  | par h₁ h₂ hd ih₁ ih₂ =>
      rintro a (ha | ha)
      · exact ih₁ a ha
      · exact ih₂ a ha

/-- **D4** (first part): at every legal Series formation `dom(θ) ⊆ 𝔸_π` — the
right arm is standalone at that moment, so `dom(θ)` is its inputs, which are
parameters by D3.  Hence a binding, once produced-valued, is never
rewritten. -/
theorem ThetaFits.paramDom {θ : Subst P K} {w₁ w₂ : W P K}
    (hθ : ThetaFits θ w₁ w₂) (h₂ : WF w₂) : θ.ParamDom := by
  intro k
  rw [← Option.not_isSome_iff_eq_none, hθ.dom_eq]
  intro hmem
  exact (h₂.inputs_isParam _ hmem).elim

/-- **D3** (second part): a parameter in `outputs(W)` lies in `inputs(W)` — a
leaf exposes a parameter only by passthrough of a slot bound to it; Series
and Par preserve the containment.  Parameters behave precisely as free
variables: composition is capture-free substitution on open terms. -/
theorem WF.param_mem_inputs_of_mem_outputs {w : W P K} (h : WF w) :
    ∀ p : P, Alloc.param p ∈ w.outputs → Alloc.param p ∈ w.inputs := by
  induction h with
  | @leaf l hβ _ =>
      rintro p ⟨k, hk⟩
      rcases l.resOut_cases k with ⟨_, hres⟩ | ⟨j, _, hres⟩
      · rw [hres] at hk; cases hk
      · exact ⟨j, hres ▸ hk⟩
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro p hp
      have hpd : θ.ParamDom := hθ.paramDom h₂
      rw [show (w₁.mkSeries w₂ θ).outputs = (w₂.rebind θ).outputs from rfl,
          W.outputs_rebind hpd] at hp
      obtain ⟨b, hb, hab⟩ := hp
      match b, hb with
      | .prod k, hb =>
          rw [hpd.apply_prod] at hab
          cases hab
      | .param q, hb =>
          cases hq : θ (.param q) with
          | some c =>
              rw [θ.apply_of_some hq] at hab
              subst hab
              exact ih₁ p (hθ.codom _ _ hq)
          | none =>
              have hqi : (θ (Alloc.param q)).isSome := (hθ.dom_eq _).mpr (ih₂ q hb)
              rw [hq] at hqi
              simp at hqi
  | par h₁ h₂ hd ih₁ ih₂ =>
      rintro p (hp | hp)
      · exact Or.inl (ih₁ p hp)
      · exact Or.inr (ih₂ p hp)

/-- **D3/D4**: every parameter occurring anywhere in a well-formed term (in
any resolved slot — i.e. in `buffers(W)`) names a member of `inputs(W)`.
So "the parameters occurring in W are exactly `inputs(W)`", and σ's adopted
set at 4.2 is `inputs(W)`. -/
theorem WF.param_mem_inputs_of_mem_buffers {w : W P K} (h : WF w) :
    ∀ p : P, Alloc.param p ∈ w.buffers → Alloc.param p ∈ w.inputs := by
  induction h with
  | @leaf l hβ hm =>
      rintro p (hp | hp)
      · exact hp
      · exact (WF.leaf hβ hm).param_mem_inputs_of_mem_outputs p hp
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro p hp
      have hpd : θ.ParamDom := hθ.paramDom h₂
      rcases hp with hp | hp
      · exact ih₁ p hp
      · rw [W.buffers_rebind hpd] at hp
        obtain ⟨b, hb, hab⟩ := hp
        match b, hb with
        | .prod k, hb =>
            rw [hpd.apply_prod] at hab
            cases hab
        | .param q, hb =>
            cases hq : θ (.param q) with
            | some c =>
                rw [θ.apply_of_some hq] at hab
                subst hab
                exact h₁.param_mem_inputs_of_mem_outputs p (hθ.codom _ _ hq)
            | none =>
                have hqi : (θ (Alloc.param q)).isSome := (hθ.dom_eq _).mpr (ih₂ q hb)
                rw [hq] at hqi
                simp at hqi
  | par h₁ h₂ hd ih₁ ih₂ =>
      rintro p (hp | hp)
      · exact Or.inl (ih₁ p hp)
      · exact Or.inr (ih₂ p hp)

/-- D3 summary form: for well-formed terms, a parameter occurs in the term
iff it is an input — free variables are exactly the interface inputs. -/
theorem WF.param_occurs_iff {w : W P K} (h : WF w) (p : P) :
    Alloc.param p ∈ w.buffers ↔ Alloc.param p ∈ w.inputs :=
  ⟨h.param_mem_inputs_of_mem_buffers p, fun hp => w.inputs_subset_buffers hp⟩

/-- **D4** (second part): every produced ID in `buffers(W)` is minted by a
node of `W` — equivalently, every ID in `buffers(W)` not minted inside `W`
lies in `inputs(W)` (with `param_mem_inputs_of_mem_buffers`). -/
theorem WF.mem_minted_of_prod_mem_buffers {w : W P K} (h : WF w) :
    ∀ k : K, Alloc.prod k ∈ w.buffers → k ∈ w.minted := by
  induction h with
  | @leaf l hβ _ =>
      rintro k (hk | hk)
      · obtain ⟨j, hj⟩ := hk
        have := hβ j
        rw [hj] at this
        cases this
      · obtain ⟨i, hi⟩ := hk
        rcases l.resOut_cases i with ⟨hfresh, hres⟩ | ⟨j, _, hres⟩
        · rw [hres] at hi
          cases hi
          exact ⟨i, hfresh, rfl⟩
        · rw [hres] at hi
          have := hβ j
          rw [hi] at this
          cases this
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      intro k hk
      have hpd : θ.ParamDom := hθ.paramDom h₂
      have hminted : (w₁.mkSeries w₂ θ).minted = w₁.minted ∪ w₂.minted := by
        simp [W.mkSeries]
      rcases hk with hk | hk
      · exact hminted ▸ Or.inl (ih₁ k hk)
      · rw [W.buffers_rebind hpd] at hk
        obtain ⟨b, hb, hab⟩ := hk
        rw [hminted]
        match b, hb with
        | .prod k', hb =>
            rw [hpd.apply_prod] at hab
            cases hab
            exact Or.inr (ih₂ k hb)
        | .param q, hb =>
            cases hq : θ (.param q) with
            | some c =>
                rw [θ.apply_of_some hq] at hab
                subst hab
                exact Or.inl (ih₁ k (w₁.outputs_subset_buffers (hθ.codom _ _ hq)))
            | none =>
                rw [θ.apply_of_none hq] at hab
                cases hab
  | par h₁ h₂ hd ih₁ ih₂ =>
      rintro k (hk | hk)
      · exact Or.inl (ih₁ k hk)
      · exact Or.inr (ih₂ k hk)

/-- Converse of D4's second part: every minted ID does occur in the term's
buffers (its minting slot resolves to it).  Together with
`mem_minted_of_prod_mem_buffers`: on well-formed terms, occurring produced
IDs = minted IDs. -/
theorem WF.prod_mem_buffers_of_mem_minted {w : W P K} (h : WF w) :
    ∀ k : K, k ∈ w.minted → Alloc.prod k ∈ w.buffers := by
  induction h with
  | @leaf l hβ _ =>
      rintro k ⟨i, hfresh, hmint⟩
      refine Or.inr ⟨i, ?_⟩
      subst hmint
      unfold LeafInst.resOut
      rw [hfresh]
  | @series w₁ w₂ θ h₁ h₂ hθ hd ih₁ ih₂ =>
      have hpd : θ.ParamDom := hθ.paramDom h₂
      intro k hk
      have hminted : (w₁.mkSeries w₂ θ).minted = w₁.minted ∪ w₂.minted := by
        simp [W.mkSeries]
      rw [hminted] at hk
      rcases hk with hk | hk
      · exact Or.inl (ih₁ k hk)
      · refine Or.inr ?_
        rw [W.buffers_rebind hpd]
        exact ⟨.prod k, ih₂ k hk, hpd.apply_prod k⟩
  | par h₁ h₂ hd ih₁ ih₂ =>
      rintro k (hk | hk)
      · exact Or.inl (ih₁ k hk)
      · exact Or.inr (ih₂ k hk)

/-- D3: at a legal Series formation, the (rewritten) right arm's inputs lie
in the left arm's outputs — `inputs(W₂) ⊆ outputs(W₁)` holds by
construction, read against current bindings. -/
theorem ThetaFits.inputs_rebind_subset_outputs {θ : Subst P K} {w₁ w₂ : W P K}
    (hθ : ThetaFits θ w₁ w₂) :
    (w₂.rebind θ).inputs ⊆ w₁.outputs := by
  rw [W.inputs_rebind]
  rintro a ⟨b, hb, hab⟩
  cases hq : θ b with
  | some c =>
      rw [θ.apply_of_some hq] at hab
      exact hab ▸ hθ.codom _ _ hq
  | none =>
      have hqi : (θ b).isSome := (hθ.dom_eq _).mpr hb
      rw [hq] at hqi
      simp at hqi

/-! ## D5: unfolded internals -/

/-- **D5** (Par): `internal(Par(W₁, W₂)) = internal(W₁) ∪ internal(W₂)`.
Needs D3 + D4: an internal ID of one branch is a produced ID minted there,
so mint-disjointness keeps it out of the sibling's interface. -/
theorem WF.internal_par {w₁ w₂ : W P K} (h₁ : WF w₁) (h₂ : WF w₂)
    (hd : MintDisjoint w₁ w₂) :
    (W.par w₁ w₂).internal = w₁.internal ∪ w₂.internal := by
  ext a
  constructor
  · rintro ⟨hb | hb, hni, hno⟩
    · exact Or.inl ⟨hb, fun h => hni (Or.inl h), fun h => hno (Or.inl h)⟩
    · exact Or.inr ⟨hb, fun h => hni (Or.inr h), fun h => hno (Or.inr h)⟩
  · -- an internal ID of a branch is produced and minted in that branch
    have key : ∀ (u v : W P K), WF u → WF v → MintDisjoint u v →
        ∀ a ∈ u.internal, a ∉ v.buffers := by
      rintro u v hu hv huv a ⟨hb, hni, _⟩ hbv
      match a with
      | .param p => exact hni (hu.param_mem_inputs_of_mem_buffers p hb)
      | .prod k =>
          exact huv k (hu.mem_minted_of_prod_mem_buffers k hb)
            (hv.mem_minted_of_prod_mem_buffers k hbv)
    rintro (⟨hb, hni, hno⟩ | ⟨hb, hni, hno⟩)
    · have hnv := key w₁ w₂ h₁ h₂ hd a ⟨hb, hni, hno⟩
      exact ⟨Or.inl hb,
        fun h => h.elim hni (fun h' => hnv (w₂.inputs_subset_buffers h')),
        fun h => h.elim hno (fun h' => hnv (w₂.outputs_subset_buffers h'))⟩
    · have hd' : MintDisjoint w₂ w₁ := fun k h h' => hd k h' h
      have hnv := key w₂ w₁ h₂ h₁ hd' a ⟨hb, hni, hno⟩
      exact ⟨Or.inr hb,
        fun h => h.elim (fun h' => hnv (w₁.inputs_subset_buffers h')) hni,
        fun h => h.elim (fun h' => hnv (w₁.outputs_subset_buffers h')) hno⟩

/-- **D5** (Series):
`internal(Series(W₁, W₂)) = internal(W₁) ∪ internal(W₂)
                          ∪ (outputs(W₁) − inputs(W₁) − outputs(W₂))`,
where per 2.4 the right-arm sets read current (rewritten) bindings — here,
the sets of `w₂.rebind θ`. -/
theorem WF.internal_mkSeries {w₁ w₂ : W P K} {θ : Subst P K}
    (h₁ : WF w₁) (h₂ : WF w₂) (hθ : ThetaFits θ w₁ w₂)
    (hd : MintDisjoint w₁ w₂) :
    (w₁.mkSeries w₂ θ).internal =
      w₁.internal ∪ (w₂.rebind θ).internal ∪
      { a | a ∈ w₁.outputs ∧ a ∉ w₁.inputs ∧ a ∉ (w₂.rebind θ).outputs } := by
  have hpd : θ.ParamDom := hθ.paramDom h₂
  ext a
  simp only [W.mem_internal, W.mkSeries, W.buffers_series, W.inputs_series,
    W.outputs_series, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb | hb, hni, hno⟩
    · by_cases ho : a ∈ w₁.outputs
      · exact Or.inr ⟨ho, hni, hno⟩
      · exact Or.inl (Or.inl ⟨hb, hni, ho⟩)
    · by_cases hi₂ : a ∈ (w₂.rebind θ).inputs
      · -- the rewritten arm's inputs lie in outputs(W₁)
        have ho : a ∈ w₁.outputs := hθ.inputs_rebind_subset_outputs hi₂
        exact Or.inr ⟨ho, hni, hno⟩
      · exact Or.inl (Or.inr ⟨hb, hi₂, hno⟩)
  · rintro ((⟨hb, hni, hno⟩ | ⟨hb, hni₂, hno⟩) | ⟨ho, hni, hno⟩)
    · -- a ∈ internal(W₁): show a ∉ outputs of the rewritten arm
      refine ⟨Or.inl hb, hni, fun ho₂ => ?_⟩
      rw [W.outputs_rebind hpd] at ho₂
      obtain ⟨b, hbo, hab⟩ := ho₂
      match b, hbo with
      | .param q, hbo =>
          have hqi : Alloc.param q ∈ w₂.inputs :=
            h₂.param_mem_inputs_of_mem_outputs q hbo
          have hsome := (hθ.dom_eq _).mpr hqi
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
          rw [θ.apply_of_some hc] at hab
          exact hno (hab ▸ hθ.codom _ _ hc)
      | .prod k, hbo =>
          rw [hpd.apply_prod] at hab
          subst hab
          exact hd k (h₁.mem_minted_of_prod_mem_buffers k hb)
            (h₂.mem_minted_of_prod_mem_buffers k (w₂.outputs_subset_buffers hbo))
    · -- a ∈ internal(rewritten W₂): show a ∉ inputs(W₁)
      refine ⟨Or.inr hb, fun hi₁ => ?_, hno⟩
      -- a non-input buffer of the rewritten arm is produced …
      rw [W.buffers_rebind hpd] at hb
      obtain ⟨b, hbb, hab⟩ := hb
      match b, hbb with
      | .param q, hbb =>
          have hqi : Alloc.param q ∈ w₂.inputs :=
            h₂.param_mem_inputs_of_mem_buffers q hbb
          have hsome := (hθ.dom_eq _).mpr hqi
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
          -- then a is the image of an input of w₂, contradicting hni₂
          exact hni₂ (by
            rw [W.inputs_rebind]
            exact ⟨.param q, hqi, hab⟩)
      | .prod k, hbb =>
          -- … while inputs(W₁) are parameters
          rw [hpd.apply_prod] at hab
          subst hab
          exact (h₁.inputs_isParam _ hi₁).elim
    · -- a ∈ outputs(W₁) − inputs(W₁) − outputs(rewritten W₂)
      exact ⟨Or.inl (w₁.outputs_subset_buffers ho), hni, hno⟩

end WorkGraph
