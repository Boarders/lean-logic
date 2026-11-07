import Logic.Propositional.Traversal

/-!
# Structural rules of natural deduction
-/

namespace Logic.Propositional

variable {α : Type} {s : LogicalStrength} {Γ Δ : Ctx (Formula α)} {φ ψ : Formula α}

/-- Replace each hypothesis by a derivation of it. -/
def Pf.subst (σ : Sub (Pf s) Γ Δ) (p : Pf s Γ φ) : Pf s Δ φ :=
  Pf.traverse
  (Pf.Traversal.syntactic
     (V := Pf s)
     (rename := Pf.rename)
     (var := id)
     (freshVar := .hyp .Z)
     (liftStrength := id))
     σ p


/-- Cut: use a derivation of `φ` in place of the hypothesis `φ`. -/
def Pf.cut (p : Pf s Γ φ) (q : Pf s (Γ ▹ φ) ψ) : Pf s Γ ψ := q.subst (.single p)

/-- Move a derivation along any map of hypotheses, which may reorder or merge them. -/
def Pf.weakenMap (f : ∀ {a}, a ∈ᵥ Γ → a ∈ᵥ Δ) (p : Pf s Γ φ) : Pf s Δ φ :=
  p.subst (.ofVarMap f)

/-- Weakening along list inclusion -/
def Pf.weaken [DecidableEq α] (h : Γ ⊆ Δ) (p : Pf s Γ φ) : Pf s Δ φ :=
  p.weakenMap fun x => Mem.ofMem (h x.toMem)

/-- Lift a derivation from a weaker logic to a stronger one. -/
def Pf.mono {s' : LogicalStrength} (h : s ≤ s') (p : Pf s Γ φ) : Pf s' Γ φ :=
  Pf.traverse
  (Pf.Traversal.syntactic
    (V := Pf s')
    (rename := Pf.rename)
    (var := id)
    (freshVar := (.hyp .Z))
    (liftStrength := (le_trans · h)))
  (Sub.id Γ)
  p

end Logic.Propositional
