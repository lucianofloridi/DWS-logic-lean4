import Mathlib
/-!
# Designable Worlds Semantics (DWS)
A Lean 4 formalisation of core results from:
**The Conduction Connective: An Irreducible Extension of Intuitionistic Modal Logic IK**
-/
universe u
namespace DWS
abbrev PropVar := ℕ
inductive Formula : Type where
  | var  : PropVar → Formula
  | bot  : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | imp  : Formula → Formula → Formula
  | box  : Formula → Formula
  | dia  : Formula → Formula
  | cond : Formula → Formula → Formula
  deriving DecidableEq, Repr
namespace Formula
def neg (φ : Formula) : Formula := imp φ bot
def top : Formula := imp bot bot
def mdepth : Formula → ℕ
  | .var _ => 0 | .bot => 0
  | .conj φ ψ | .disj φ ψ | .imp φ ψ => max φ.mdepth ψ.mdepth
  | .box φ | .dia φ => φ.mdepth + 1
  | .cond φ ψ => max φ.mdepth ψ.mdepth + 1
end Formula
structure BareFrame (W : Type u) where
  le : W → W → Prop
  R  : W → W → Prop
  le_refl  : ∀ w, le w w
  le_trans : ∀ w v u, le w v → le v u → le w u
  fc : ∀ w w' u, le w w' → R w u → ∃ u', R w' u' ∧ le u u'
def BareFrame.S {W : Type u} (F : BareFrame W) (w u : W) : Prop :=
  F.R w u ∧ F.le w u
def BareFrame.SSerial {W : Type u} (F : BareFrame W) : Prop :=
  ∀ w, ∃ u, F.S w u
structure Model (W : Type u) extends BareFrame W where
  V : PropVar → Set W
  V_mono : ∀ p w w', le w w' → w ∈ V p → w' ∈ V p
def sat {W : Type u} (M : Model W) : W → Formula → Prop
  | w, .var p     => w ∈ M.V p
  | _, .bot       => False
  | w, .conj φ ψ  => sat M w φ ∧ sat M w ψ
  | w, .disj φ ψ  => sat M w φ ∨ sat M w ψ
  | w, .imp φ ψ   => ∀ v, M.le w v → sat M v φ → sat M v ψ
  | w, .box φ     => ∀ v, M.le w v → ∀ u, M.R v u → sat M u φ
  | w, .dia φ     => ∃ u, M.R w u ∧ sat M u φ
  | w, .cond φ ψ  => ∀ v, M.le w v → sat M v φ →
                        ∃ u, M.toBareFrame.S v u ∧ sat M u ψ
theorem persistence {W : Type u} (M : Model W) (w w' : W)
    (hle : M.le w w') (φ : Formula) :
    sat M w φ → sat M w' φ := by
  induction φ generalizing w w' with
  | var p => exact M.V_mono p w w' hle
  | bot => intro h; exact h
  | conj φ ψ ih1 ih2 =>
    intro ⟨h1, h2⟩; exact ⟨ih1 w w' hle h1, ih2 w w' hle h2⟩
  | disj φ ψ ih1 ih2 =>
    intro h; cases h with
    | inl h => exact Or.inl (ih1 w w' hle h)
    | inr h => exact Or.inr (ih2 w w' hle h)
  | imp φ ψ _ _ =>
    intro h v hle' hφ; exact h v (M.le_trans w w' v hle hle') hφ
  | box φ _ =>
    intro h v hle' u hR; exact h v (M.le_trans w w' v hle hle') u hR
  | dia φ ih =>
    intro ⟨u, hR, hφ⟩
    obtain ⟨u', hR', hle_u⟩ := M.fc w w' u hle hR
    exact ⟨u', hR', ih u u' hle_u hφ⟩
  | cond φ ψ _ _ =>
    intro h v hle' hφ; exact h v (M.le_trans w w' v hle hle') hφ
theorem C1_valid {W : Type u} (M : Model W) (hSer : M.toBareFrame.SSerial)
    (w : W) (φ ψ : Formula) :
    sat M w (.imp (.box (.imp φ ψ)) (.cond φ ψ)) := by
  intro v hle hBox v' hle' hφ
  obtain ⟨u, hR_u, hle_u⟩ := hSer v'
  have hφ_u := persistence M v' u hle_u φ hφ
  have hBox_v' := hBox v' hle'
  have hImp_u := hBox_v' u hR_u
  exact ⟨u, ⟨hR_u, hle_u⟩, hImp_u u (M.le_refl u) hφ_u⟩
theorem C2_valid {W : Type u} (M : Model W)
    (w : W) (φ ψ : Formula) :
    sat M w (.imp (.cond φ ψ) (.imp φ (.dia ψ))) := by
  intro v hle hCond v' hle' hφ
  have hCond_v' := persistence M v v' hle' (.cond φ ψ) hCond
  obtain ⟨u, ⟨hR, _⟩, hψ⟩ := hCond_v' v' (M.le_refl v') hφ
  exact ⟨u, hR, hψ⟩
theorem C3_valid {W : Type u} (M : Model W)
    (w : W) (φ ψ χ : Formula) :
    sat M w (.imp (.conj (.cond φ ψ) (.box (.imp ψ χ)))
                  (.cond φ χ)) := by
  intro v hle ⟨hCond, hBoxImp⟩ v' hle' hφ
  obtain ⟨u, ⟨hR, hle_u⟩, hψ⟩ := hCond v' hle' hφ
  have hχ := hBoxImp v' hle' u hR u (M.le_refl u) hψ
  exact ⟨u, ⟨hR, hle_u⟩, hχ⟩
theorem CP_valid {W : Type u} (M : Model W)
    (w : W) (φ ψ α : Formula) :
    sat M w (.imp (.conj (.cond φ ψ) α)
                  (.cond φ (.conj ψ α))) := by
  intro v hle ⟨hCond, hα⟩ v' hle' hφ
  obtain ⟨u, hS, hψ⟩ := hCond v' hle' hφ
  have hα_u := persistence M v u (M.le_trans v v' u hle' hS.2) α hα
  exact ⟨u, hS, hψ, hα_u⟩
theorem CW_valid {W : Type u} (M : Model W)
    (w : W) (φ ψ α : Formula) :
    sat M w (.imp (.imp α φ) (.imp (.cond φ ψ) (.cond α ψ))) := by
  intro v hle hαφ v' hle' hCond v'' hle'' hα
  have hαφ_v'' := persistence M v v''
    (M.le_trans v v' v'' hle' hle'') (.imp α φ) hαφ
  have hφ := hαφ_v'' v'' (M.le_refl v'') hα
  have hCond_v'' := persistence M v' v'' hle'' (.cond φ ψ) hCond
  exact hCond_v'' v'' (M.le_refl v'') hφ
theorem SP_valid {W : Type u} (M : Model W)
    (w : W) (φ ψ : Formula) :
    sat M w (.imp (.cond φ ψ) (.cond φ (.conj ψ φ))) := by
  intro v hle hCond v' hle' hφ
  obtain ⟨u, hS, hψ⟩ := hCond v' hle' hφ
  exact ⟨u, hS, hψ, persistence M v' u hS.2 φ hφ⟩
theorem SSerial_implies_alpha_dia_alpha {W : Type u} (M : Model W)
    (hSer : M.toBareFrame.SSerial) (w : W) (φ : Formula) :
    sat M w (.imp φ (.dia φ)) := by
  intro v hle hφ
  obtain ⟨u, hRu, hle_u⟩ := hSer v
  exact ⟨u, hRu, persistence M v u hle_u φ hφ⟩
end DWS
