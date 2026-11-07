import Logic.Propositional.Structural
import Mathlib.Tactic

/-!
# Example derivations
-/

namespace Logic.Propositional

variable {α : Type} {s : LogicalStrength} {Γ : Ctx (Formula α)} {φ ψ χ : Formula α}
  [DecidableEq α]

/-! ## Primitive negation agrees with `φ ⇒ ⊥`, in minimal logic -/

def neg_imp_ff : Pf .minimal Γ (¬ₚ φ ⇒ₚ (φ ⇒ₚ .ff)) := by
  apply Pf.impI
  apply Pf.impI
  apply Pf.notE <;> by_hyp

def imp_ff_neg : Pf .minimal Γ ((φ ⇒ₚ .ff) ⇒ₚ ¬ₚ φ) := by
  apply Pf.impI
  apply Pf.notI
  apply Pf.impE <;> by_hyp


/-! ## Minimal logic proves the double negation of excluded middle -/
def not_not_lem : Pf .minimal Γ (¬ₚ ¬ₚ (φ ∨ₚ ¬ₚ φ)) := by
  apply Pf.notI
  apply Pf.notE (φ := φ ∨ₚ ¬ₚ φ)
  · by_hyp
  · apply Pf.orI₂
    apply Pf.notI
    apply Pf.notE (φ := φ ∨ₚ ¬ₚ φ)
    · by_hyp
    · apply Pf.orI₁
      by_hyp

/-! ## Ex falso as a formula, from intuitionistic logic up -/

def ff_imp : Pf .intuitionistic Γ (.ff ⇒ₚ φ) := by
  apply Pf.impI
  apply Pf.ex_falso (by rfl)
  · by_hyp

/-! ## Reductio ad absurdum as a derived rule in classical logic -/
def raa (h : .classical ≤ s) : Pf s (Γ ▹ ¬ₚ φ) .ff → Pf s Γ φ := by
  intro φ_contra
  apply Pf.orE (φ := φ) (ψ := ¬ₚφ)
  · apply Pf.lem h
  · by_hyp
  · have h_le : LogicalStrength.intuitionistic <= s := by
      trans .classical
      · rfl
      · exact h
    apply Pf.ex_falso h_le
    exact φ_contra

/-! ## Using `rename` and `cut` -/

/-- Implication is transitive; the premises must be weakened under the new hypothesis `φ`. -/
def imp_trans : Pf s Γ (φ ⇒ₚ ψ) → Pf s Γ (ψ ⇒ₚ χ) → Pf s Γ (φ ⇒ₚ χ) := by
  intro h1 h2
  apply Pf.impI
  apply Pf.wk (ψ := φ) at h1
  apply Pf.wk (ψ := φ) at h2
  apply Pf.impE h2
  apply Pf.impE h1
  by_hyp

/-- Flatten a conjunction on the left. -/
def Pf.andL_inv : Pf s (Γ ▹ (φ ∧ₚ ψ)) χ → Pf s (Γ ▹ φ ▹ ψ) χ := by
  intro h
  apply Pf.cut (φ := φ ∧ₚ ψ)
  · apply Pf.andI <;> by_hyp
  · apply h.weaken (by grind)

/-- Replace two hypotheses by their conjunction. -/
def Pf.andL : Pf s (Γ ▹ φ ▹ ψ) χ → Pf s (Γ ▹ (φ ∧ₚ ψ)) χ := by
  intro h
  apply Pf.cut (φ := φ) (.andE₁ (by by_hyp))
  apply Pf.cut (φ := ψ) (.andE₂ (by by_hyp))
  exact h.weaken (by grind)

/-- Bind both halves of conjunction as hypotheses. -/
def andLet : Pf s Γ (φ ∧ₚ ψ) → Pf s (Γ ▹ φ ▹ ψ) χ → Pf s Γ χ := by
  intro h1 h2
  apply Pf.cut h1
  apply Pf.andL
  exact h2

end Logic.Propositional
