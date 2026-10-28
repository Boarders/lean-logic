import Mathlib.Logic.Basic

/-!
# Contexts, de Bruijn indices and thinnings

Generic contexts shared by every logic in the project: a context is a list whose head is the
most recent entry (de Bruijn index 0).
-/

namespace Logic

universe u

abbrev Ctx (α : Type u) := List α

/-- snoc notation for contexts -/
scoped notation:67 Γ:67 " ▹ " t:68 => List.cons t Γ

/-- Type-valued de Bruijn indices -/
inductive Mem {α : Type u} : α → Ctx α → Type u where
  | Z : ∀ {Γ a}, Mem a (Γ ▹ a)
  | S : ∀ {Γ a b}, Mem a Γ → Mem a (Γ ▹ b)

scoped infix:50 " ∈ᵥ " => Mem

variable {α : Type u}

/-- Order-preserving embeddings (thinnings): `Ren Γ Δ` says `Γ` is a subsequence of `Δ`. -/
inductive Ren : Ctx α → Ctx α → Type u where
  | done : Ren [] []
  | keep : ∀ {Γ Δ a}, Ren Γ Δ → Ren (Γ ▹ a) (Δ ▹ a)
  | drop : ∀ {Γ Δ a}, Ren Γ Δ → Ren Γ (Δ ▹ a)

namespace Ren

def id : (Γ : Ctx α) → Ren Γ Γ
  | [] => done
  | _ :: Γ => keep (id Γ)

/-- Push a renaming under a binder. -/
abbrev lift {Γ Δ : Ctx α} {a : α} (ρ : Ren Γ Δ) : Ren (Γ ▹ a) (Δ ▹ a) := keep ρ

/-- The one-step weakening `Γ ⊆ Γ ▹ a`. -/
abbrev wk {Γ : Ctx α} {a : α} : Ren Γ (Γ ▹ a) := drop (id Γ)

/-- Act on a variable. -/
def var {Γ Δ : Ctx α} {a : α} : Ren Γ Δ → a ∈ᵥ Γ → a ∈ᵥ Δ
  | keep _, .Z => .Z
  | keep ρ, .S x => .S (var ρ x)
  | drop ρ, x => .S (var ρ x)

/-- Composition in function order: `σ.comp ρ` is `ρ` followed by `σ`. -/
def comp {Γ Δ Θ : Ctx α} : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
  | done, ρ => ρ
  | keep σ, keep ρ => keep (comp σ ρ)
  | keep σ, drop ρ => drop (comp σ ρ)
  | drop σ, ρ => drop (comp σ ρ)

@[simp] theorem var_id {Γ : Ctx α} {a : α} (x : a ∈ᵥ Γ) : (id Γ).var x = x := by
  induction x with
  | Z => rfl
  | S x ih => exact congrArg Mem.S ih

@[simp] theorem var_comp {Γ Δ Θ : Ctx α} (σ : Ren Δ Θ) (ρ : Ren Γ Δ) {a : α} (x : a ∈ᵥ Γ) :
    (σ.comp ρ).var x = σ.var (ρ.var x) := by
  induction σ generalizing Γ with
  | done => cases ρ; cases x
  | keep σ ih =>
    cases ρ with
    | keep ρ =>
      cases x with
      | Z => rfl
      | S x => exact congrArg Mem.S (ih ρ x)
    | drop ρ => exact congrArg Mem.S (ih ρ x)
  | drop σ ih => exact congrArg Mem.S (ih ρ x)

@[simp] theorem id_comp {Γ Δ : Ctx α} (ρ : Ren Γ Δ) : (id Δ).comp ρ = ρ := by
  induction ρ with
  | done => rfl
  | keep ρ ih => exact congrArg keep ih
  | drop ρ ih => exact congrArg drop ih

@[simp] theorem comp_id {Γ Δ : Ctx α} (ρ : Ren Γ Δ) : ρ.comp (id Γ) = ρ := by
  induction ρ with
  | done => rfl
  | keep ρ ih => exact congrArg keep ih
  | drop ρ ih => exact congrArg drop ih

theorem comp_assoc {Γ Δ Θ Ξ : Ctx α} (τ : Ren Θ Ξ) (σ : Ren Δ Θ) (ρ : Ren Γ Δ) :
    (τ.comp σ).comp ρ = τ.comp (σ.comp ρ) := by
  induction τ generalizing Γ Δ with
  | done => rfl
  | keep τ ih =>
    cases σ with
    | keep σ =>
      cases ρ with
      | keep ρ => exact congrArg keep (ih σ ρ)
      | drop ρ => exact congrArg drop (ih σ ρ)
    | drop σ => exact congrArg drop (ih σ ρ)
  | drop τ ih => exact congrArg drop (ih σ ρ)

end Ren

end Logic
