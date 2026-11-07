namespace Logic.Propositional

inductive BinOp where
  | or | and | implies : BinOp
  deriving DecidableEq

inductive Formula (α : Type) where
  | atom : α → Formula α
  | bin  : BinOp → Formula α → Formula α → Formula α
  | not : Formula α → Formula α
  | ff   : Formula α
  | tt : Formula α
  deriving DecidableEq

/-! Precedences follow Lean's own: `¬` 40, `∧` 35, `∨` 30, `→` 25; binary ones right-associative. -/
scoped notation:max "¬ₚ " φ:40 => Formula.not φ
scoped notation:35 φ:36 " ∧ₚ " ψ:35 => Formula.bin BinOp.and φ ψ
scoped notation:30 φ:31 " ∨ₚ " ψ:30 => Formula.bin BinOp.or φ ψ
scoped notation:25 φ:26 " ⇒ₚ " ψ:25 => Formula.bin BinOp.implies φ ψ

def Formula.fold (atomβ : α → β) (ffβ ttβ : β) (notβ : β → β) (opβ : BinOp → β → β → β) : Formula α → β
  | .atom a => atomβ a
  | .bin opName a b => opβ opName (fold atomβ ffβ ttβ notβ opβ a) (fold atomβ ffβ ttβ notβ opβ b)
  | .not a => notβ (fold atomβ ffβ ttβ notβ opβ a)
  | .tt => ttβ
  | .ff => ffβ

section
variable (atomβ : α → β) (ffβ ttβ : β) (notβ : β → β) (opβ : BinOp → β → β → β)

@[simp] theorem Formula.fold_atom (a : α) :
    (Formula.atom a).fold atomβ ffβ ttβ notβ opβ = atomβ a := rfl
@[simp] theorem Formula.fold_bin (o : BinOp) (φ ψ : Formula α) :
    (Formula.bin o φ ψ).fold atomβ ffβ ttβ notβ opβ =
      opβ o (φ.fold atomβ ffβ ttβ notβ opβ) (ψ.fold atomβ ffβ ttβ notβ opβ) := rfl
@[simp] theorem Formula.fold_not (φ : Formula α) :
    (Formula.not φ).fold atomβ ffβ ttβ notβ opβ = notβ (φ.fold atomβ ffβ ttβ notβ opβ) := rfl
@[simp] theorem Formula.fold_tt : (Formula.tt : Formula α).fold atomβ ffβ ttβ notβ opβ = ttβ := rfl
@[simp] theorem Formula.fold_ff : (Formula.ff : Formula α).fold atomβ ffβ ttβ notβ opβ = ffβ := rfl

end

def Formula.bind : (φ : Formula α) → (σ : α → Formula β) → Formula β :=
  fun φ σ => fold σ ff tt not bin φ

instance : Monad Formula where
 pure := .atom
 bind := Formula.bind

open Formula
@[simp] theorem bind_atom' (a : α) (σ : α → Formula β) : (atom a).bind σ = σ a := rfl
@[simp] theorem bind_bin  : (bin o φ ψ).bind σ = bin o (φ.bind σ) (ψ.bind σ) := rfl
@[simp] theorem bind_not  : (¬ₚ φ).bind σ = ¬ₚ (φ.bind σ) := rfl
@[simp] theorem bind_tt   : (tt).bind σ = tt := rfl
@[simp] theorem bind_ff   : (ff).bind σ = ff := rfl

@[simp] theorem bind_atom (φ : Formula α) : φ.bind atom = φ := by
  induction φ <;> simp_all

theorem bind_bind (φ : Formula α) (f : α → Formula β) (g : β → Formula γ) : (φ.bind f).bind g = φ.bind (fun a => (f a).bind g) := by
  induction φ <;> simp_all

instance : LawfulMonad Formula := LawfulMonad.mk' _
  (id_map := bind_atom)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_bind)


end Logic.Propositional
