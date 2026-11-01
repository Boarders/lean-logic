import Logic.Prelude.Context

/-!
# Substitutions

A substitution `Sub T Γ Δ` gives one `T Δ a` for each entry `a` of `Γ`: what each variable of `Γ`
is replaced by, living over `Δ`. It is first-order data (a snoc-list), so two substitutions are
equal when their entries are, with no function extensionality.

`T` is the syntax that variables are replaced by (terms, derivations, ...). What is generic here
is everything that does not traverse `T`; each syntax supplies its own `subst`.
-/

namespace Logic

universe u v w

variable {A : Type u}

/-- A syntax indexed by a context that can be moved along thinnings. -/
class Thinnable (T : Ctx A → A → Type v) where
  rename : ∀ {Γ Δ a}, Ren Γ Δ → T Γ a → T Δ a

/-- A thinnable syntax that has variables. -/
class VarLike (T : Ctx A → A → Type v) extends Thinnable T where
  var : ∀ {Γ a}, a ∈ᵥ Γ → T Γ a

class LawfulThinnable (T : Ctx A → A → Type v) [Thinnable T] : Prop where
  rename_id : ∀ {Γ a} (t : T Γ a), Thinnable.rename (Ren.id Γ) t = t
  rename_comp : ∀ {Γ Δ Θ a} (σ : Ren Δ Θ) (ρ : Ren Γ Δ) (t : T Γ a),
    Thinnable.rename (σ.comp ρ) t = Thinnable.rename σ (Thinnable.rename ρ t)

class LawfulVarLike (T : Ctx A → A → Type v) [VarLike T] : Prop extends LawfulThinnable T where
  rename_var : ∀ {Γ Δ a} (ρ : Ren Γ Δ) (x : a ∈ᵥ Γ),
    Thinnable.rename ρ (VarLike.var (T := T) x) = VarLike.var (ρ.var x)

/-- Substitutions: one `T Δ a` for each entry `a` of `Γ`. -/
inductive Sub (T : Ctx A → A → Type v) : Ctx A → Ctx A → Type (max u v) where
  | nil : ∀ {Δ}, Sub T [] Δ
  | cons : ∀ {Γ Δ a}, Sub T Γ Δ → T Δ a → Sub T (Γ ▹ a) Δ

namespace Sub

variable {T : Ctx A → A → Type v} {U : Ctx A → A → Type w}

/-- Look up the entry for a variable. -/
def var : ∀ {Γ Δ : Ctx A} {a : A}, Sub T Γ Δ → a ∈ᵥ Γ → T Δ a
  | _, _, _, cons _ t, .Z => t
  | _, _, _, cons σ _, .S x => var σ x

/-- Build a substitution from its lookup function. -/
def tabulate {Δ : Ctx A} : ∀ {Γ : Ctx A}, (∀ {a}, a ∈ᵥ Γ → T Δ a) → Sub T Γ Δ
  | [], _ => nil
  | _ :: _, f => cons (tabulate fun x => f (.S x)) (f .Z)

/-- Apply a function to every entry. -/
def map {Δ Θ : Ctx A} (f : ∀ {a}, T Δ a → U Θ a) : ∀ {Γ : Ctx A}, Sub T Γ Δ → Sub U Γ Θ
  | _, nil => nil
  | _, cons σ t => cons (map f σ) (f t)

/-- Keep only the entries a thinning selects. -/
def select : ∀ {Γ Δ Θ : Ctx A}, Ren Γ Δ → Sub T Δ Θ → Sub T Γ Θ
  | _, _, _, .done, nil => nil
  | _, _, _, .keep ρ, cons σ t => cons (select ρ σ) t
  | _, _, _, .drop ρ, cons σ _ => select ρ σ

/-- Two substitutions are equal when they agree on every variable. -/
theorem ext : ∀ {Γ Δ : Ctx A} {σ τ : Sub T Γ Δ},
    (∀ {a} (x : a ∈ᵥ Γ), σ.var x = τ.var x) → σ = τ
  | _, _, nil, nil, _ => rfl
  | _, _, cons σ t, cons τ u, h => by
    rw [ext fun x => h (.S x), show t = u from h .Z]

@[simp] theorem var_tabulate {Γ Δ : Ctx A} (f : ∀ {a}, a ∈ᵥ Γ → T Δ a) {a : A} (x : a ∈ᵥ Γ) :
    (tabulate f).var x = f x := by
  induction x with
  | Z => rfl
  | S x ih => exact ih _

@[simp] theorem var_map {Δ Θ : Ctx A} (f : ∀ {a}, T Δ a → U Θ a) :
    ∀ {Γ : Ctx A} (σ : Sub T Γ Δ) {a : A} (x : a ∈ᵥ Γ), (σ.map f).var x = f (σ.var x)
  | _, cons _ _, _, .Z => rfl
  | _, cons σ _, _, .S x => var_map f σ x

@[simp] theorem var_select {Γ Δ Θ : Ctx A} (ρ : Ren Γ Δ) (σ : Sub T Δ Θ) {a : A} (x : a ∈ᵥ Γ) :
    (σ.select ρ).var x = σ.var (ρ.var x) := by
  induction ρ generalizing Θ with
  | done => cases x
  | keep ρ ih =>
    cases σ with
    | cons σ t =>
      cases x with
      | Z => rfl
      | S x => exact ih σ x
  | drop ρ ih =>
    cases σ with
    | cons σ t => exact ih σ x

@[simp] theorem map_id {Γ Δ : Ctx A} (σ : Sub T Γ Δ) : σ.map (fun t => t) = σ :=
  ext fun x => by simp

theorem map_map {V : Ctx A → A → Type w} {Γ Δ Θ Ξ : Ctx A} (f : ∀ {a}, T Δ a → U Θ a)
    (g : ∀ {a}, U Θ a → V Ξ a) (σ : Sub T Γ Δ) :
    (σ.map f).map g = σ.map (fun t => g (f t)) :=
  ext fun x => by simp

@[simp] theorem select_id {Γ Δ : Ctx A} (σ : Sub T Γ Δ) : σ.select (Ren.id Γ) = σ :=
  ext fun x => by simp

theorem select_comp {Γ Δ Θ Ξ : Ctx A} (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) (σ : Sub T Θ Ξ) :
    σ.select (ρ'.comp ρ) = (σ.select ρ').select ρ :=
  ext fun x => by simp

theorem map_select {Γ Δ Θ Ξ : Ctx A} (f : ∀ {a}, T Θ a → U Ξ a) (ρ : Ren Γ Δ) (σ : Sub T Δ Θ) :
    (σ.select ρ).map f = (σ.map f).select ρ :=
  ext fun x => by simp

/-! ## Operations that need to know about `T` -/

section Thinnable

variable [Thinnable T]

/-- Move every entry along a thinning of the target context. -/
def weaken {Γ Δ Θ : Ctx A} (ρ : Ren Δ Θ) (σ : Sub T Γ Δ) : Sub T Γ Θ :=
  σ.map (Thinnable.rename ρ)

@[simp] theorem var_weaken {Γ Δ Θ : Ctx A} (ρ : Ren Δ Θ) (σ : Sub T Γ Δ) {a : A} (x : a ∈ᵥ Γ) :
    (σ.weaken ρ).var x = Thinnable.rename ρ (σ.var x) :=
  var_map _ σ x

theorem weaken_id [LawfulThinnable T] {Γ Δ : Ctx A} (σ : Sub T Γ Δ) :
    σ.weaken (Ren.id Δ) = σ :=
  ext fun x => by simp [LawfulThinnable.rename_id]

theorem weaken_comp [LawfulThinnable T] {Γ Δ Θ Ξ : Ctx A} (ρ' : Ren Θ Ξ) (ρ : Ren Δ Θ)
    (σ : Sub T Γ Δ) : σ.weaken (ρ'.comp ρ) = (σ.weaken ρ).weaken ρ' :=
  ext fun x => by simp [LawfulThinnable.rename_comp]

end Thinnable

section VarLike

variable [VarLike T]

/-- The identity substitution: every variable is replaced by itself. -/
def id (Γ : Ctx A) : Sub T Γ Γ := tabulate VarLike.var

/-- Each variable is replaced by its image along a thinning. -/
def ofRen {Γ Δ : Ctx A} (ρ : Ren Γ Δ) : Sub T Γ Δ := tabulate fun x => VarLike.var (ρ.var x)

/-- Push a substitution under a binder. -/
def lift {Γ Δ : Ctx A} {a : A} (σ : Sub T Γ Δ) : Sub T (Γ ▹ a) (Δ ▹ a) :=
  cons (σ.weaken Ren.wk) (VarLike.var .Z)

/-- Replace the newest variable by `t` and leave the rest alone. -/
def single {Γ : Ctx A} {a : A} (t : T Γ a) : Sub T (Γ ▹ a) Γ := cons (id Γ) t

@[simp] theorem var_id {Γ : Ctx A} {a : A} (x : a ∈ᵥ Γ) :
    (id (T := T) Γ).var x = VarLike.var x :=
  var_tabulate _ x

@[simp] theorem var_ofRen {Γ Δ : Ctx A} (ρ : Ren Γ Δ) {a : A} (x : a ∈ᵥ Γ) :
    (ofRen (T := T) ρ).var x = VarLike.var (ρ.var x) :=
  var_tabulate _ x

@[simp] theorem var_lift_Z {Γ Δ : Ctx A} {a : A} (σ : Sub T Γ Δ) :
    (σ.lift (a := a)).var .Z = VarLike.var .Z := rfl

@[simp] theorem var_lift_S {Γ Δ : Ctx A} {a b : A} (σ : Sub T Γ Δ) (x : b ∈ᵥ Γ) :
    (σ.lift (a := a)).var (.S x) = Thinnable.rename Ren.wk (σ.var x) :=
  var_weaken _ σ x

@[simp] theorem var_single_Z {Γ : Ctx A} {a : A} (t : T Γ a) : (single t).var .Z = t := rfl

@[simp] theorem var_single_S {Γ : Ctx A} {a b : A} (t : T Γ a) (x : b ∈ᵥ Γ) :
    (single t).var (.S x) = VarLike.var x :=
  var_id x

theorem ofRen_id {Γ : Ctx A} : ofRen (T := T) (Ren.id Γ) = id Γ :=
  ext fun x => by simp

theorem lift_id [LawfulVarLike T] {Γ : Ctx A} {a : A} : (id (T := T) Γ).lift (a := a) = id (Γ ▹ a) :=
  ext fun x => by
    cases x with
    | Z => rfl
    | S x => simp [LawfulVarLike.rename_var]

theorem lift_ofRen [LawfulVarLike T] {Γ Δ : Ctx A} {a : A} (ρ : Ren Γ Δ) :
    (ofRen (T := T) ρ).lift (a := a) = ofRen ρ.keep :=
  ext fun x => by
    cases x with
    | Z => rfl
    | S x => simp [LawfulVarLike.rename_var]

end VarLike

end Sub

end Logic
