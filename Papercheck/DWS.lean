import Mathlib

universe u

abbrev Var := Nat

inductive Form : Type
  | atom : Var → Form
  | bot  : Form
  | and  : Form → Form → Form
  | or   : Form → Form → Form
  | imp  : Form → Form → Form
  | box  : Form → Form
  | dia  : Form → Form
  | cond : Form → Form → Form
deriving DecidableEq

/-- ▷-free fragment predicate (IK fragment). -/
def LIK : Form → Prop
  | Form.atom _   => True
  | Form.bot      => True
  | Form.and φ ψ  => LIK φ ∧ LIK ψ
  | Form.or φ ψ   => LIK φ ∧ LIK ψ
  | Form.imp φ ψ  => LIK φ ∧ LIK ψ
  | Form.box φ    => LIK φ
  | Form.dia φ    => LIK φ
  | Form.cond _ _ => False

structure BareFrame (W : Type u) where
  le  : W → W → Prop
  R   : W → W → Prop
  refl : ∀ w, le w w
  trans : ∀ {w v u}, le w v → le v u → le w u
  confluence :
    ∀ {w w' u},
      le w w' →
      R w u →
      ∃ u', R w' u' ∧ le u u'

/-- Enriched frame: adds Aff and Con (semantically inert). -/
structure EnrichedFrame (W : Type u) extends BareFrame W where
  Aff : W → Set W
  Con : W → Set Form
  /-- (F4) afforded moves are R-moves. -/
  Aff_sound : ∀ {w u}, u ∈ Aff w → R w u

abbrev PropVal (W : Type u) := Var → Set W

def Persistent {W : Type u} (le : W → W → Prop) (V : PropVal W) : Prop :=
  ∀ n w v, le w v → w ∈ V n → v ∈ V n

/-- Bare model. -/
structure Model (W : Type u) where
  F : BareFrame W
  V : PropVal W
  pers : Persistent F.le V

namespace Sem

def Sat {W : Type u} (M : Model W) : W → Form → Prop
  | w, Form.atom n    => w ∈ M.V n
  | _, Form.bot       => False
  | w, Form.and φ ψ   => Sat M w φ ∧ Sat M w ψ
  | w, Form.or φ ψ    => Sat M w φ ∨ Sat M w ψ
  | w, Form.imp φ ψ   =>
      ∀ v, M.F.le w v → Sat M v φ → Sat M v ψ
  | w, Form.box φ     =>
      ∀ v, M.F.le w v → ∀ u, M.F.R v u → Sat M u φ
  | w, Form.dia φ     =>
      ∃ u, M.F.R w u ∧ Sat M u φ
  | w, Form.cond φ ψ  =>
      ∀ v, M.F.le w v → Sat M v φ →
        ∃ u, M.F.R v u ∧ M.F.le v u ∧ Sat M u ψ

def Not (φ : Form) : Form := Form.imp φ Form.bot
def Top : Form := Form.imp Form.bot Form.bot

/-- (F10) seriality for specification-preserving witnesses: ∀v ∃u (vRu ∧ v≤u). -/
def Serial {W : Type u} (F : BareFrame W) : Prop :=
  ∀ v : W, ∃ u : W, F.R v u ∧ F.le v u

/-- Validity on all models and all worlds (bare semantics). -/
def Valid (φ : Form) : Prop :=
  ∀ {W : Type u}, (M : Model W) → (w : W) → Sat M w φ

/-- Persistence. -/
theorem persistence
  {W : Type u} (M : Model W) :
  ∀ (φ : Form) (w v : W),
    Sat M w φ →
    M.F.le w v →
    Sat M v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro w v hw hle
      exact M.pers n w v hle hw
  | bot =>
      intro w v hw _
      exact hw
  | and φ ψ ihφ ihψ =>
      intro w v hw hle
      rcases hw with ⟨hφ, hψ⟩
      exact ⟨ihφ w v hφ hle, ihψ w v hψ hle⟩
  | or φ ψ ihφ ihψ =>
      intro w v hw hle
      cases hw with
      | inl h => exact Or.inl (ihφ w v h hle)
      | inr h => exact Or.inr (ihψ w v h hle)
  | imp φ ψ _ _ =>
      intro w v hw hle x hx hφx
      exact hw x (M.F.trans hle hx) hφx
  | box φ _ =>
      intro w v hw hle x hx u hR
      exact hw x (M.F.trans hle hx) u hR
  | dia φ ih =>
      intro w v hw hle
      rcases hw with ⟨u0, hR, hu⟩
      rcases M.F.confluence hle hR with ⟨u1, hR', huu'⟩
      exact ⟨u1, hR', ih u0 u1 hu huu'⟩
  | cond φ ψ _ _ =>
      intro w v hw hle x hx hφx
      rcases hw x (M.F.trans hle hx) hφx with ⟨u, hR, hle2, hu⟩
      exact ⟨u, hR, hle2, hu⟩

/-- C5: □(φ→ψ) → (φ ▷ ψ), assuming Serial (F10). -/
theorem C5
  {W : Type u} (M : Model W) (w0 : W) (φ ψ : Form)
  (hSerial : Serial M.F) :
  Sat M w0 (Form.imp (Form.box (Form.imp φ ψ)) (Form.cond φ ψ)) := by
  intro v hvle hBox v2 hvle2 hφv2
  rcases hSerial v2 with ⟨u, hRu, hv2u⟩
  have hImp_at_u : Sat M u (Form.imp φ ψ) := hBox v2 hvle2 u hRu
  have hφu : Sat M u φ := persistence M φ v2 u hφv2 hv2u
  have hψu : Sat M u ψ := hImp_at_u u (M.F.refl u) hφu
  exact ⟨u, hRu, hv2u, hψu⟩

/-- (i) (φ ▷ ⊥) ↔ ¬φ. -/
theorem boundary_i
  {W : Type u} (M : Model W) (w : W) (φ : Form) :
  Sat M w (Form.imp (Form.cond φ Form.bot) (Not φ)) ∧
  Sat M w (Form.imp (Not φ) (Form.cond φ Form.bot)) := by
  constructor
  · intro v hvle hcond v2 hvle2 hφ
    rcases hcond v2 hvle2 hφ with ⟨u, _hR, _hle, hu⟩
    exact hu
  · intro v hvle hnotφ v2 hvle2 hφ
    have : False := hnotφ v2 hvle2 hφ
    exact False.elim this

/-- (ii) ((φ ∨ ψ) ▷ χ) ↔ (φ ▷ χ) ∧ (ψ ▷ χ). -/
theorem boundary_ii
  {W : Type u} (M : Model W) (w : W) (φ ψ χ : Form) :
  (Sat M w (Form.imp (Form.cond (Form.or φ ψ) χ) (Form.and (Form.cond φ χ) (Form.cond ψ χ)))) ∧
  (Sat M w (Form.imp (Form.and (Form.cond φ χ) (Form.cond ψ χ)) (Form.cond (Form.or φ ψ) χ))) := by
  constructor
  · intro v hvle hcond
    refine ⟨?_, ?_⟩
    · intro v2 hvle2 hφ
      have hor : Sat M v2 (Form.or φ ψ) := Or.inl hφ
      rcases hcond v2 hvle2 hor with ⟨u, hR, hle, hχ⟩
      exact ⟨u, hR, hle, hχ⟩
    · intro v2 hvle2 hψ
      have hor : Sat M v2 (Form.or φ ψ) := Or.inr hψ
      rcases hcond v2 hvle2 hor with ⟨u, hR, hle, hχ⟩
      exact ⟨u, hR, hle, hχ⟩
  · intro v hvle hand v2 hvle2 hor
    rcases hand with ⟨hφ, hψ⟩
    cases hor with
    | inl h =>
        rcases hφ v2 hvle2 h with ⟨u, hR, hle, hχ⟩
        exact ⟨u, hR, hle, hχ⟩
    | inr h =>
        rcases hψ v2 hvle2 h with ⟨u, hR, hle, hχ⟩
        exact ⟨u, hR, hle, hχ⟩

/-- (iii) (φ ▷ (ψ ∧ χ)) → (φ ▷ ψ) ∧ (φ ▷ χ). -/
theorem boundary_iii
  {W : Type u} (M : Model W) (w : W) (φ ψ χ : Form) :
  Sat M w (Form.imp (Form.cond φ (Form.and ψ χ)) (Form.and (Form.cond φ ψ) (Form.cond φ χ))) := by
  intro v hvle hcond
  refine ⟨?_, ?_⟩
  · intro v2 hvle2 hφ
    rcases hcond v2 hvle2 hφ with ⟨u, hR, hle, hψχ⟩
    exact ⟨u, hR, hle, hψχ.1⟩
  · intro v2 hvle2 hφ
    rcases hcond v2 hvle2 hφ with ⟨u, hR, hle, hψχ⟩
    exact ⟨u, hR, hle, hψχ.2⟩

/-- IK satisfaction: same as Sat for all connectives except Form.cond, which is always False. -/
def IKSat {W : Type u} (M : Model W) : W → Form → Prop
  | w, Form.atom n    => w ∈ M.V n
  | _, Form.bot       => False
  | w, Form.and φ ψ   => IKSat M w φ ∧ IKSat M w ψ
  | w, Form.or φ ψ    => IKSat M w φ ∨ IKSat M w ψ
  | w, Form.imp φ ψ   =>
      ∀ v, M.F.le w v → IKSat M v φ → IKSat M v ψ
  | w, Form.box φ     =>
      ∀ v, M.F.le w v → ∀ u, M.F.R v u → IKSat M u φ
  | w, Form.dia φ     =>
      ∃ u, M.F.R w u ∧ IKSat M u φ
  | _, Form.cond _ _  => False

/-- IK validity: valid in all bare models under IKSat. -/
def IKValid (φ : Form) : Prop :=
  ∀ (W : Type u) (M : Model W) (w : W), IKSat M w φ

/-- For LIK formulas, Sat and IKSat agree pointwise. -/
theorem IKSat_iff_Sat {W : Type u} (M : Model W) :
    ∀ (φ : Form), LIK φ → ∀ (w : W), Sat M w φ ↔ IKSat M w φ := by
  intro φ
  induction φ with
  | atom n => intro _ w; exact Iff.rfl
  | bot    => intro _ w; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro ⟨hφ, hψ⟩ w
      exact and_congr (ihφ hφ w) (ihψ hψ w)
  | or φ ψ ihφ ihψ =>
      intro ⟨hφ, hψ⟩ w
      exact or_congr (ihφ hφ w) (ihψ hψ w)
  | imp φ ψ ihφ ihψ =>
      intro ⟨hφ, hψ⟩ w
      constructor
      · intro h v hle hik
        exact (ihψ hψ v).mp (h v hle ((ihφ hφ v).mpr hik))
      · intro h v hle hsat
        exact (ihψ hψ v).mpr (h v hle ((ihφ hφ v).mp hsat))
  | box φ ihφ =>
      intro hφ w
      constructor
      · intro h v hle u hR
        exact (ihφ hφ u).mp (h v hle u hR)
      · intro h v hle u hR
        exact (ihφ hφ u).mpr (h v hle u hR)
  | dia φ ihφ =>
      intro hφ w
      constructor
      · intro ⟨u, hR, hu⟩
        exact ⟨u, hR, (ihφ hφ u).mp hu⟩
      · intro ⟨u, hR, hu⟩
        exact ⟨u, hR, (ihφ hφ u).mpr hu⟩
  | cond _ _ _ _ =>
      intro hcond
      exact hcond.elim

/-- Conservative extension: DWS validity and IK validity coincide on LIK formulas. -/
theorem conservative_extension (φ : Form) (hφ : LIK φ) :
    Valid.{u} φ ↔ IKValid.{u} φ := by
  constructor
  · intro hv W M w
    exact (IKSat_iff_Sat M φ hφ w).mp (hv M w)
  · intro hiv W M w
    exact (IKSat_iff_Sat M φ hφ w).mpr (hiv W M w)

end Sem

open Sem

inductive C5W1 where | w deriving DecidableEq
open C5W1

def C5_le1 : C5W1 → C5W1 → Prop := fun a b => a = b
def C5_R0  : C5W1 → C5W1 → Prop := fun _ _ => False

lemma C5_le1_refl : ∀ x : C5W1, C5_le1 x x := by
  intro x
  rfl

lemma C5_le1_trans : ∀ {a b c : C5W1}, C5_le1 a b → C5_le1 b c → C5_le1 a c := by
  intro a b c hab hbc
  exact Eq.trans hab hbc

lemma C5_confl_vacuous :
  ∀ {x x' y : C5W1}, C5_le1 x x' → C5_R0 x y → ∃ y', C5_R0 x' y' ∧ C5_le1 y y' := by
  intro x x' y _ hR
  cases hR

def C5_F1 : BareFrame C5W1 :=
{ le := C5_le1
  R := C5_R0
  refl := C5_le1_refl
  trans := by
    intro a b c
    exact C5_le1_trans
  confluence := by
    intro x x' y
    exact C5_confl_vacuous }

def C5_V1 : PropVal C5W1 := fun _ => ∅

lemma C5_V1_pers : Persistent C5_F1.le C5_V1 := by
  intro _n w v _hle hw
  cases hw

def C5_M1 : Model C5W1 :=
{ F := C5_F1
  V := C5_V1
  pers := C5_V1_pers }

lemma C5_box_top_to_bot_holds : Sat C5_M1 w (Form.box (Form.imp Top Form.bot)) := by
  intro v hvle u hR
  cases hR

lemma C5_top_cond_bot_fails : ¬ Sat C5_M1 w (Form.cond Top Form.bot) := by
  intro hcond
  have hTop : Sat C5_M1 w Top := by
    intro v hvle hvbot
    exact hvbot
  rcases hcond w (C5_M1.F.refl w) hTop with ⟨u, hR, _, _⟩
  cases hR

theorem C5_not_valid_without_serial :
  ¬ Sat C5_M1 w (Form.imp (Form.box (Form.imp Top Form.bot)) (Form.cond Top Form.bot)) := by
  intro h
  have hBox := C5_box_top_to_bot_holds
  have hCond := h w (C5_M1.F.refl w) hBox
  exact C5_top_cond_bot_fails hCond

namespace Enrichment

open Sem

/-- Enriched model = enriched frame + persistent valuation. -/
structure EModel (W : Type u) where
  F : EnrichedFrame W
  V : PropVal W
  pers : Persistent F.le V

/-- Reduct of an enriched model to a bare model by forgetting Aff and Con. -/
def reduct {W : Type u} (EM : EModel W) : Model W :=
{ F := { le := EM.F.le
         R := EM.F.R
         refl := EM.F.refl
         trans := EM.F.trans
         confluence := EM.F.confluence }
  V := EM.V
  pers := EM.pers }

/-- Satisfaction in an enriched model is defined via its reduct. -/
def ESat {W : Type u} (EM : EModel W) : W → Form → Prop :=
  Sat (reduct EM)

/-- Aff/Con reduct conservativity. -/
theorem aff_con_reduct
  {W : Type u} (EM : EModel W) (w : W) (φ : Form) :
  ESat EM w φ ↔ Sat (reduct EM) w φ := by
  rfl

/-- (F7) constraint persistence along ≤. -/
def F7 {W : Type u} (EM : EModel W) : Prop :=
  ∀ {w w' : W}, EM.F.le w w' → EM.F.Con w ⊆ EM.F.Con w'

/-- (F8) affordance/constraint consistency along R. -/
def F8 {W : Type u} (EM : EModel W) : Prop :=
  ∀ (w u : W), EM.F.R w u → ∀ ψ, ψ ∈ EM.F.Con w → ESat EM u ψ

/-- (F9) constraint self-satisfaction. -/
def F9 {W : Type u} (EM : EModel W) : Prop :=
  ∀ (w : W) (ψ : Form), ψ ∈ EM.F.Con w → ESat EM w ψ

/-- (C0) joint satisfiability, semantic version. -/
def C0 {W : Type u} (EM : EModel W) : Prop :=
  ∀ (w : W), ∀ ψ, ψ ∈ EM.F.Con w → ESat EM w ψ

theorem C0_iff_F9 {W : Type u} (EM : EModel W) : C0 EM ↔ F9 EM := by
  rfl

/-- C3 inside the enriched setting, using F7 and F9. -/
theorem C3_enriched
  {W : Type u} (EM : EModel W)
  (hF7 : F7 EM) (hF9 : F9 EM)
  (w0 : W) (φ ψ χ : Form) (hχ : χ ∈ EM.F.Con w0) :
  ESat EM w0 (Form.imp (Form.cond (Form.and φ χ) ψ) (Form.cond φ ψ)) := by
  change Sat (reduct EM) w0 (Form.imp (Form.cond (Form.and φ χ) ψ) (Form.cond φ ψ))
  intro v hvle hcond v2 hvle2 hφ
  have hwv2 : (reduct EM).F.le w0 v2 := (reduct EM).F.trans hvle hvle2
  have hχ' : χ ∈ EM.F.Con v2 := (hF7 hwv2) hχ
  have hv2χ : Sat (reduct EM) v2 χ := by
    have : ESat EM v2 χ := hF9 v2 χ hχ'
    simpa [ESat] using this
  have hφχ : Sat (reduct EM) v2 (Form.and φ χ) := ⟨hφ, hv2χ⟩
  rcases hcond v2 hvle2 hφχ with ⟨u, hR, hle, hψ⟩
  exact ⟨u, hR, hle, hψ⟩

end Enrichment

namespace Bisim
open Sem

structure IKBisim
  {W₁ : Type u} {W₂ : Type u}
  (M₁ : Model W₁) (M₂ : Model W₂)
  (Z : W₁ → W₂ → Prop) : Prop where
  atoms :
    ∀ {w₁ : W₁} {w₂ : W₂} {n : Var},
      Z w₁ w₂ →
      (Sat M₁ w₁ (Form.atom n) ↔ Sat M₂ w₂ (Form.atom n))
  le_forth :
    ∀ {w₁ : W₁} {w₂ : W₂} {v₁ : W₁},
      Z w₁ w₂ →
      M₁.F.le w₁ v₁ →
      ∃ v₂, M₂.F.le w₂ v₂ ∧ Z v₁ v₂
  le_back :
    ∀ {w₁ : W₁} {w₂ : W₂} {v₂ : W₂},
      Z w₁ w₂ →
      M₂.F.le w₂ v₂ →
      ∃ v₁, M₁.F.le w₁ v₁ ∧ Z v₁ v₂
  R_forth :
    ∀ {w₁ : W₁} {w₂ : W₂} {x₁ : W₁},
      Z w₁ w₂ →
      M₁.F.R w₁ x₁ →
      ∃ x₂, M₂.F.R w₂ x₂ ∧ Z x₁ x₂
  R_back :
    ∀ {w₁ : W₁} {w₂ : W₂} {x₂ : W₂},
      Z w₁ w₂ →
      M₂.F.R w₂ x₂ →
      ∃ x₁, M₁.F.R w₁ x₁ ∧ Z x₁ x₂

theorem invariance
  {W₁ : Type u} {W₂ : Type u}
  {M₁ : Model W₁} {M₂ : Model W₂}
  {Z : W₁ → W₂ → Prop}
  (hB : IKBisim M₁ M₂ Z) :
  ∀ {φ : Form} {w₁ : W₁} {w₂ : W₂},
    LIK φ → Z w₁ w₂ → (Sat M₁ w₁ φ ↔ Sat M₂ w₂ φ) := by
  intro φ
  induction φ with
  | atom n =>
      intro w₁ w₂ hLIK hZ
      simpa using hB.atoms hZ
  | bot =>
      intro w₁ w₂ hLIK hZ
      constructor <;> intro h <;> exact h
  | and φ ψ ihφ ihψ =>
      intro w₁ w₂ hLIK hZ
      rcases hLIK with ⟨hLIKφ, hLIKψ⟩
      constructor
      · intro h
        exact ⟨(ihφ hLIKφ hZ).mp h.1, (ihψ hLIKψ hZ).mp h.2⟩
      · intro h
        exact ⟨(ihφ hLIKφ hZ).mpr h.1, (ihψ hLIKψ hZ).mpr h.2⟩
  | or φ ψ ihφ ihψ =>
      intro w₁ w₂ hLIK hZ
      rcases hLIK with ⟨hLIKφ, hLIKψ⟩
      constructor
      · intro h
        cases h with
        | inl hφ => exact Or.inl ((ihφ hLIKφ hZ).mp hφ)
        | inr hψ => exact Or.inr ((ihψ hLIKψ hZ).mp hψ)
      · intro h
        cases h with
        | inl hφ => exact Or.inl ((ihφ hLIKφ hZ).mpr hφ)
        | inr hψ => exact Or.inr ((ihψ hLIKψ hZ).mpr hψ)
  | imp φ ψ ihφ ihψ =>
      intro w₁ w₂ hLIK hZ
      rcases hLIK with ⟨hLIKφ, hLIKψ⟩
      constructor
      · intro hImp v₂ hv₂ hφ₂
        rcases hB.le_back hZ hv₂ with ⟨v₁, hv₁, hZv⟩
        have hφ₁ : Sat M₁ v₁ φ := (ihφ hLIKφ hZv).mpr hφ₂
        have hψ₁ : Sat M₁ v₁ ψ := hImp v₁ hv₁ hφ₁
        exact (ihψ hLIKψ hZv).mp hψ₁
      · intro hImp v₁ hv₁ hφ₁
        rcases hB.le_forth hZ hv₁ with ⟨v₂, hv₂, hZv⟩
        have hφ₂ : Sat M₂ v₂ φ := (ihφ hLIKφ hZv).mp hφ₁
        have hψ₂ : Sat M₂ v₂ ψ := hImp v₂ hv₂ hφ₂
        exact (ihψ hLIKψ hZv).mpr hψ₂
  | box φ ih =>
      intro w₁ w₂ hLIK hZ
      constructor
      · intro hBox v₂ hv₂ x₂ hRx₂
        rcases hB.le_back hZ hv₂ with ⟨v₁, hv₁, hZv⟩
        rcases hB.R_back hZv hRx₂ with ⟨x₁, hRx₁, hZx⟩
        have hφ₁ : Sat M₁ x₁ φ := hBox v₁ hv₁ x₁ hRx₁
        exact (ih hLIK hZx).mp hφ₁
      · intro hBox v₁ hv₁ x₁ hRx₁
        rcases hB.le_forth hZ hv₁ with ⟨v₂, hv₂, hZv⟩
        rcases hB.R_forth hZv hRx₁ with ⟨x₂, hRx₂, hZx⟩
        have hφ₂ : Sat M₂ x₂ φ := hBox v₂ hv₂ x₂ hRx₂
        exact (ih hLIK hZx).mpr hφ₂
  | dia φ ih =>
      intro w₁ w₂ hLIK hZ
      constructor
      · intro hDia
        rcases hDia with ⟨x₁, hRx₁, hφ₁⟩
        rcases hB.R_forth hZ hRx₁ with ⟨x₂, hRx₂, hZx⟩
        exact ⟨x₂, hRx₂, (ih hLIK hZx).mp hφ₁⟩
      · intro hDia
        rcases hDia with ⟨x₂, hRx₂, hφ₂⟩
        rcases hB.R_back hZ hRx₂ with ⟨x₁, hRx₁, hZx⟩
        exact ⟨x₁, hRx₁, (ih hLIK hZx).mpr hφ₂⟩
  | cond φ ψ ihφ ihψ =>
      intro w₁ w₂ hLIK hZ
      cases hLIK

end Bisim

namespace IrredSep
open Sem
open Bisim

abbrev p : Form := Form.atom 0
abbrev q : Form := Form.atom 1

inductive WM where
  | w
  | u
deriving DecidableEq

inductive WN where
  | wp
  | up
deriving DecidableEq

open WM
open WN

def leM : WM → WM → Prop
  | .w, .w => True
  | .w, .u => True
  | .u, .u => True
  | .u, .w => False

def RM : WM → WM → Prop
  | .w, .u => True
  | .u, .u => True
  | _, _   => False

lemma leM_refl : ∀ x : WM, leM x x := by
  intro x
  cases x <;> simp [leM]

lemma leM_trans : ∀ {a b c : WM}, leM a b → leM b c → leM a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp [leM] at hab hbc ⊢

lemma M_confl :
  ∀ {x x' y : WM}, leM x x' → RM x y → ∃ y', RM x' y' ∧ leM y y' := by
  intro x x' y hle hR
  cases x <;> cases x' <;> cases y <;> simp [leM, RM] at hle hR ⊢
  · exact ⟨WM.u, by simp [RM, leM]⟩
  · exact ⟨WM.u, by simp [RM, leM]⟩
  · exact ⟨WM.u, by simp [RM, leM]⟩

def FM : BareFrame WM :=
{ le := leM
  R := RM
  refl := leM_refl
  trans := by
    intro a b c
    exact leM_trans
  confluence := by
    intro x x' y
    exact M_confl }

def leN : WN → WN → Prop
  | .wp, .wp => True
  | .up, .up => True
  | _, _     => False

def RN : WN → WN → Prop
  | .wp, .up => True
  | .up, .up => True
  | _, _     => False

lemma leN_refl : ∀ x : WN, leN x x := by
  intro x
  cases x <;> simp [leN]

lemma leN_trans : ∀ {a b c : WN}, leN a b → leN b c → leN a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp [leN] at hab hbc ⊢

lemma N_confl :
  ∀ {x x' y : WN}, leN x x' → RN x y → ∃ y', RN x' y' ∧ leN y y' := by
  intro x x' y hle hR
  cases x <;> cases x' <;> cases y <;> simp [leN, RN] at hle hR ⊢
  · exact ⟨WN.up, by simp [RN, leN]⟩
  · exact ⟨WN.up, by simp [RN, leN]⟩

def FN : BareFrame WN :=
{ le := leN
  R := RN
  refl := leN_refl
  trans := by
    intro a b c
    exact leN_trans
  confluence := by
    intro x x' y
    exact N_confl }

def VallM : PropVal WM := fun _ => Set.univ
def VallN : PropVal WN := fun _ => Set.univ

lemma VallM_pers : Persistent FM.le VallM := by
  intro n w v hle hw
  simp [VallM]

lemma VallN_pers : Persistent FN.le VallN := by
  intro n w v hle hw
  simp [VallN]

def MM : Model WM :=
{ F := FM
  V := VallM
  pers := VallM_pers }

def NN : Model WN :=
{ F := FN
  V := VallN
  pers := VallN_pers }

def Z : WM → WN → Prop := fun _ _ => True

lemma Z_bisim : IKBisim MM NN Z := by
  refine
    { atoms := ?_
      le_forth := ?_
      le_back := ?_
      R_forth := ?_
      R_back := ?_ }
  · intro w₁ w₂ n hZ
    constructor <;> intro _ <;> exact Set.mem_univ _
  · intro w₁ w₂ v₁ hZ hle
    exact ⟨w₂, leN_refl w₂, trivial⟩
  · intro w₁ w₂ v₂ hZ hle
    exact ⟨w₁, leM_refl w₁, trivial⟩
  · intro w₁ w₂ x₁ hZ hR
    cases w₂ <;> exact ⟨WN.up, trivial, trivial⟩
  · intro w₁ w₂ x₂ hZ hR
    cases w₁ <;> exact ⟨WM.u, trivial, trivial⟩

lemma M_w_cond_true : Sem.Sat MM WM.w (Form.cond p q) := by
  intro v hvle hp
  cases v with
  | w => exact ⟨WM.u, trivial, trivial, Set.mem_univ _⟩
  | u => exact ⟨WM.u, trivial, trivial, Set.mem_univ _⟩

lemma N_wp_cond_false : ¬ Sem.Sat NN WN.wp (Form.cond p q) := by
  intro h
  have hp : Sem.Sat NN WN.wp p := Set.mem_univ _
  have h' := h WN.wp (leN_refl WN.wp) hp
  rcases h' with ⟨x, hRx, hlex, _⟩
  cases x with
  | wp => exact hRx.elim
  | up => exact hlex.elim

end IrredSep
