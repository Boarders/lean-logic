import Logic.Prelude.Context
import Logic.Propositional.Syntax
import Mathlib.Order.Defs.LinearOrder

namespace Logic.Propositional

inductive LogicalStrength where
  | minimal | intuitionistic | classical
  deriving DecidableEq

namespace LogicalStrength

def le : LogicalStrength → LogicalStrength → Bool
  | minimal, _ => true
  | intuitionistic, minimal => false
  | intuitionistic, _ => true
  | classical, classical => true
  | classical, _ => false

instance : LE LogicalStrength := ⟨fun a b => le a b⟩
instance : DecidableRel (α := LogicalStrength) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (le a b))

instance : LinearOrder LogicalStrength where
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  le_total a b := by cases a <;> cases b <;> decide
  toDecidableLE := inferInstance

end LogicalStrength

inductive Pf {α : Type} (s : LogicalStrength) : Ctx (Formula α) → Formula α → Type where
  | hyp : ∀ {Γ φ}, φ ∈ᵥ Γ → Pf s Γ φ
  | ttI : ∀ {Γ}, Pf s Γ .tt
  | andI : ∀ {Γ φ ψ}, Pf s Γ φ → Pf s Γ ψ → Pf s Γ (φ ∧ₚ ψ)
  | andE₁ : ∀ {Γ φ ψ}, Pf s Γ (φ ∧ₚ ψ) → Pf s Γ φ
  | andE₂ : ∀ {Γ φ ψ}, Pf s Γ (φ ∧ₚ ψ) → Pf s Γ ψ
  | orI₁ : ∀ {Γ φ ψ}, Pf s Γ φ → Pf s Γ (φ ∨ₚ ψ)
  | orI₂ : ∀ {Γ φ ψ}, Pf s Γ ψ → Pf s Γ (φ ∨ₚ ψ)
  | orE : ∀ {Γ φ ψ χ}, Pf s Γ (φ ∨ₚ ψ) → Pf s (Γ ▹ φ) χ → Pf s (Γ ▹ ψ) χ → Pf s Γ χ
  | impI : ∀ {Γ φ ψ}, Pf s (Γ ▹ φ) ψ → Pf s Γ (φ ⇒ₚ ψ)
  | impE : ∀ {Γ φ ψ}, Pf s Γ (φ ⇒ₚ ψ) → Pf s Γ φ → Pf s Γ ψ
  | notI : ∀ {Γ φ}, Pf s (Γ ▹ φ) .ff → Pf s Γ (¬ₚ φ)
  | notE : ∀ {Γ φ}, Pf s Γ (¬ₚ φ) → Pf s Γ φ → Pf s Γ .ff
  | lem : ∀ {Γ φ}, .classical ≤ s → Pf s Γ (φ ∨ₚ ¬ₚ φ)
  | ex_falso : ∀ {Γ φ}, .intuitionistic ≤ s → Pf s Γ .ff → Pf s Γ φ

end Logic.Propositional
