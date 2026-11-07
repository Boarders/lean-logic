import Logic.Prelude.Context
import Logic.Prelude.Sub
import Logic.Propositional.Syntax
import Mathlib.Order.Defs.LinearOrder
import Batteries.CodeAction

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

/-- Close a goal `Pf s Γ φ` by a hypothesis, when `φ` occurs in `Γ`. -/
macro "by_hyp" : tactic => `(tactic| (apply Logic.Propositional.Pf.hyp; find_mem))

def Pf.rename {Γ Δ : Ctx (Formula α)} (σ : Ren Γ Δ) (P : Pf s Γ φ) : Pf s Δ φ :=
  match P with
  | .hyp p => .hyp (Ren.var σ p)
  | .ttI => .ttI
  | .andI p q => .andI (p.rename σ) (q.rename σ)
  | .andE₁ p => .andE₁ (p.rename σ)
  | .andE₂ p => .andE₂ (p.rename σ)
  | .orI₁ p => .orI₁ (p.rename σ)
  | .orI₂ p => .orI₂ (p.rename σ)
  | .orE pq p q => .orE (pq.rename σ) (p.rename (σ.keep)) (q.rename (σ.keep))
  | .impI p => .impI (p.rename (σ.keep))
  | .impE p q => .impE (p.rename σ) (q.rename σ)
  | .notI p => .notI (p.rename (σ.keep))
  | .notE p q => .notE (p.rename σ) (q.rename σ)
  | .lem h => .lem h
  | .ex_falso h p => .ex_falso h (p.rename σ)

theorem Pf.rename_id {Γ : Ctx (Formula α)} (P : Pf s Γ φ) : P.rename (Ren.id Γ) = P := by
  induction P  <;> simp_all [rename, Ren.id]

theorem Pf.rename_comp
  {α : Type} {Γ Δ Θ : Ctx (Formula α)} {φ : Formula α} (σ : Ren Δ Θ) (ρ : Ren Γ Δ) (P : Pf s Γ φ) : P.rename (σ.comp ρ) = (P.rename ρ).rename σ := by
  induction P generalizing Δ Θ <;> simp_all [rename, ← Ren.keep_comp_keep]

instance {α : Type} {S : LogicalStrength} : Thinnable (Pf (α := α) S) where
  rename := Pf.rename

instance {α : Type} {S : LogicalStrength} : LawfulThinnable (Pf (α := α) S) where
  rename_id := Pf.rename_id
  rename_comp := Pf.rename_comp

instance {α : Type} {S : LogicalStrength}  : VarLike (Pf (α := α) S) where
  var := Pf.hyp

theorem Pf.rename_var {α : Type}{S} {Γ Δ : Ctx (Formula α)} {a : Formula α} (ρ : Ren Γ Δ) (x : a ∈ᵥ Γ) :
    Pf.rename ρ (Pf.hyp (s := S) x) = Pf.hyp (ρ.var x) := by
  simp [rename]

instance {α : Type} {S : LogicalStrength}  : LawfulVarLike (Pf (α := α) S) where
  rename_var := Pf.rename_var

/-- Weaken a derivation by one new hypothesis. -/
def Pf.wk {Γ : Ctx (Formula α)} {φ ψ : Formula α} (p : Pf s Γ φ) : Pf s (Γ ▹ ψ) φ :=
  p.rename Ren.wk

/-- Weaken a derivation by a whole context of new hypotheses. -/
def Pf.wkCtx (Δ : Ctx (Formula α)) {Γ : Ctx (Formula α)} {φ : Formula α} (p : Pf s Γ φ) :
    Pf s (Δ ++ Γ) φ :=
  p.rename (Ren.wkCtx Δ)

end Logic.Propositional
