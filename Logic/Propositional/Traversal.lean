import Logic.Propositional.NaturalDeduction
import Batteries.CodeAction

/-!
# Generic traversals of derivations

A traversal has two families:
  V C : (Γ : Ctxt)  → (φ : Formula) → Type

We then can conceptually think of V as how we interpret contexts and for which we have
an action by renamings (it is a presheaf on Ren) and C as how we interpret formulas
and so e.g we interpret var as a map:

  V Γ φ → C Γ φ

For binders we then have terms that inductively take a term Kripke V C of the form:

  Kripke ::= (σ : Ren Δ Θ) → (v : V Θ a) → C Θ b

We can think about σ as how to extend our context, and `v` as how to get the value
of the variable from the new context in order to interpret the value in the extended
context.
-/

namespace Logic.Propositional

/-- A allais--chapman--mcbride--mckinna syntax traversal. -/
structure Pf.Traversal {α β : Type} (s : LogicalStrength)
    (V C : Ctx (Formula β) → Formula α → Type) where
  /-- How values are weakened along a thinning. -/
  rename : ∀ {Δ Θ : Ctx (Formula β)} {φ : Formula α}, Ren Δ Θ → V Δ φ → V Θ φ
  /-- A hypothesis: Turning a semantic variable into its value. -/
  var : ∀ {Δ φ}, V Δ φ → C Δ φ
  ttI : ∀ {Δ}, C Δ .tt
  andI : ∀ {Δ φ ψ}, C Δ φ → C Δ ψ → C Δ (φ ∧ₚ ψ)
  andE₁ : ∀ {Δ φ ψ}, C Δ (φ ∧ₚ ψ) → C Δ φ
  andE₂ : ∀ {Δ φ ψ}, C Δ (φ ∧ₚ ψ) → C Δ ψ
  orI₁ : ∀ {Δ φ ψ}, C Δ φ → C Δ (φ ∨ₚ ψ)
  orI₂ : ∀ {Δ φ ψ}, C Δ ψ → C Δ (φ ∨ₚ ψ)
  orE : ∀ {Δ φ ψ χ}, C Δ (φ ∨ₚ ψ) → Kripke V C Δ φ χ → Kripke V C Δ ψ χ → C Δ χ
  impI : ∀ {Δ φ ψ}, Kripke V C Δ φ ψ → C Δ (φ ⇒ₚ ψ)
  impE : ∀ {Δ φ ψ}, C Δ (φ ⇒ₚ ψ) → C Δ φ → C Δ ψ
  notI : ∀ {Δ φ}, Kripke V C Δ φ .ff → C Δ (¬ₚ φ)
  notE : ∀ {Δ φ}, C Δ (¬ₚ φ) → C Δ φ → C Δ .ff
  lem : ∀ {Δ φ}, .classical ≤ s → C Δ (φ ∨ₚ ¬ₚ φ)
  ex_falso : ∀ {Δ φ}, .intuitionistic ≤ s → C Δ .ff → C Δ φ

/-- Turn a traversal of a body over `Γ ▹ φ` into a Kripke body: weaken the environment along the given thinning and then add the given value for the newly bound value. -/
def Pf.Traversal.under {α β : Type} {s : LogicalStrength}
    {V C : Ctx (Formula β) → Formula α → Type} (T : Pf.Traversal s V C)
    {Γ : Ctx (Formula α)} {Δ : Ctx (Formula β)} {φ ψ : Formula α}
    (σ : Sub V Γ Δ) (k : ∀ {Θ}, Sub V (Γ ▹ φ) Θ → C Θ ψ) : Kripke V C Δ φ ψ :=
  fun ren v => k (.cons (σ.map (T.rename ren)) v)

/-- Run a traversal over a derivation, starting from an environment for its hypotheses. -/
def Pf.traverse {α β : Type} {s : LogicalStrength} {V C : Ctx (Formula β) → Formula α → Type}
    (T : Pf.Traversal s V C) {Γ : Ctx (Formula α)} {Δ : Ctx (Formula β)} {φ : Formula α}
    (σ : Sub V Γ Δ) (pf : Pf s Γ φ) : C Δ φ :=
  go σ pf
where
  go {Γ Δ φ} (σ : Sub V Γ Δ) : Pf s Γ φ → C Δ φ
  | .hyp x => T.var (σ.var x)
  | .ttI => T.ttI
  | .andI p q => T.andI (go σ p) (go σ q)
  | .andE₁ p => T.andE₁ (go σ p)
  | .andE₂ p => T.andE₂ (go σ p)
  | .orI₁ p => T.orI₁ (go σ p)
  | .orI₂ p => T.orI₂ (go σ p)
  | .orE d p q => T.orE (go σ d) (T.under σ (go · p)) (T.under σ (go · q))
  | .impI p => T.impI (T.under σ (go · p))
  | .impE p q => T.impE (go σ p) (go σ q)
  | .notI p => T.notI (T.under σ (go · p))
  | .notE p q => T.notE (go σ p) (go σ q)
  | .lem g => T.lem g
  | .ex_falso g p => T.ex_falso g (go σ p)

/-- The traversal that rebuilds every rule unchanged, into derivations of strength `s'`.
The various arguments stand for the following:
- `V` abstract type for values that hypotheses stand for
- `var` turns a value into a derivation
- `fresh` is the value of a newly bound hypothesis
- `guard` explains how to strengthen the logic
-/
def Pf.Traversal.syntactic {α : Type} {s s' : LogicalStrength}
    {V : Ctx (Formula α) → Formula α → Type}
    (rename : ∀ {Δ Θ : Ctx (Formula α)} {φ : Formula α}, Ren Δ Θ → V Δ φ → V Θ φ)
    (var : ∀ {Δ φ}, V Δ φ → Pf s' Δ φ)
    (freshVar : ∀ {Δ φ}, V (Δ ▹ φ) φ)
    (liftStrength : ∀ {t : LogicalStrength}, t ≤ s → t ≤ s') :
    Pf.Traversal s V (Pf s') where
  rename := rename
  var := var
  ttI := .ttI
  andI := .andI
  andE₁ := .andE₁
  andE₂ := .andE₂
  orI₁ := .orI₁
  orI₂ := .orI₂
  orE d k₁ k₂ := .orE d (k₁ Ren.wk freshVar) (k₂ Ren.wk freshVar)
  impI k := .impI (k Ren.wk freshVar)
  impE := .impE
  notI k := .notI (k Ren.wk freshVar)
  notE := .notE
  lem g := .lem (liftStrength g)
  ex_falso g p := .ex_falso (liftStrength g) p

end Logic.Propositional
