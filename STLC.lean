inductive Ty where
  | arrow (ty₁ ty₂ : Ty)
  | top
  deriving DecidableEq

notation "⊤" => Ty.top

inductive Term where
  | var (fvar : Nat)
  | abs (ty : Ty) (body : Term)
  | app (t₁ t₂ : Term)

inductive Value where
  | abs (ty : Ty) (body : Term)

instance : Coe Value Term where
  coe | .abs ty body => .abs ty body

-- Note: We use this representation of contexts to ensure that each variable is only assigned at
--       most once. This technically enables infinite contexts, but that's not an issue.
def Ctx := Nat → Option Ty

def Ctx.empty : Ctx :=
  fun _ => none

instance : EmptyCollection Ctx where
  emptyCollection := Ctx.empty

def Ctx.set (ctx : Ctx) (var : Nat) (ty : Ty) : Ctx :=
  fun x => if x = var then ty else ctx x

notation:max ctx "[" x " ↦ " ty  "]" => Ctx.set ctx x ty

-- Shifts all variables' indices up by 1.
def Ctx.shift (ctx : Ctx) : Ctx
  | 0     => none
  | x + 1 => ctx x

prefix:max "↥" => Ctx.shift

inductive Dir where
  | up
  | down

def Dir.move (n : Nat) : Dir → Nat
  | up   => n + 1
  | down => n - 1 

-- The shift of a term above cutoff c.
def Term.shift (dir : Dir) (c : Nat) : Term → Term
  | var x       => if x < c then var x else var (dir.move x)
  | abs ty body => abs ty <| shift dir (c + 1) body
  | app t₁ t₂   => app (shift dir c t₁) (shift dir c t₂)

prefix:max "↥" => Term.shift Dir.up 0
prefix:max "↧" => Term.shift Dir.down 0

def Term.subst (fvar : Nat) (s : Term) : Term → Term
  | var x       => if x = fvar then s else var x
  | abs ty body => abs ty <| subst (fvar + 1) ↥s body
  | app t₁ t₂   => app (subst fvar s t₁) (subst fvar s t₂)

notation:max t₁ "[" x " ↦ " t₂ "]" => Term.subst x t₂ t₁

inductive Subtypes : Ty → Ty → Prop
  | refl  : Subtypes ty ty
  | trans : Subtypes ty₁ ty₂ → Subtypes ty₂ ty₃ → Subtypes ty₁ ty₃
  | top   : Subtypes ty ⊤
  | arrow : Subtypes ty₁ ty₂ → Subtypes ty₃ ty₄ → Subtypes (.arrow ty₂ ty₃) (.arrow ty₁ ty₄)

notation:max ty₁:60 " <: " ty₂:60 => Subtypes ty₁ ty₂

inductive Eval : Term → Term → Prop
  | app₁ (t₂ : Term) : Eval t₁ t₁' → Eval (.app t₁ t₂) (.app t₁' t₂)
  | app₂ (v₁ : Value) : Eval t₂ t₂' → Eval (.app v₁ t₂) (.app v₁ t₂')
  | beta (ty : Ty) (t : Term) (v : Value) : Eval (.app (.abs ty t) v) ↧(t[0 ↦ ↥v])
 
infixr:50 " ⇒ " => Eval 

inductive Types : Ctx → Term → Ty → Prop
  | var : ctx x = some ty → Types ctx (.var x) ty
  | abs : Types (↥ctx)[0 ↦ ty₁] t ty₂ → Types ctx (.abs ty₁ t) (.arrow ty₁ ty₂)
  | app : Types ctx t₁ (.arrow ty₁ ty₂) → Types ctx t₂ ty₁ → Types ctx (.app t₁ t₂) ty₂
  | sub : Types ctx t ty₁ → ty₁ <: ty₂ → Types ctx t ty₂

notation ctx " ⊢ " t " ⋮ " ty => Types ctx t ty
notation      "⊢ " t " ⋮ " ty => ∅ ⊢ t ⋮ ty

theorem Subtypes.inversion_arrow (h : ty <: .arrow ty₁ ty₂) : 
    ∃ ty₃ ty₄, (ty = .arrow ty₃ ty₄) ∧ (ty₃ <: ty₁) ∧ (ty₂ <: ty₄) := by
  generalize h' : Ty.arrow ty₁ ty₂ = ty'
  rw [h'] at h
  induction h
  case refl => exact ⟨ty₁, ty₂, h'.symm, .refl, .refl⟩
  case trans => sorry
  case top => contradiction
  case arrow ty₂ ty₃ _ h₁ h₂ hi₁ hi₂ =>
    injection h' with ht₁ ht₂
    subst ht₁ ht₂
    sorry

theorem inversion_var : (ctx ⊢ .var x ⋮ ty) → ctx x = ty
  | .var h => h
  | .sub ht hs => sorry

theorem inversion_abs : 
    (ctx ⊢ .abs ty₁ t ⋮ ty) → ∃ ty₂, (ty = .arrow ty₁ ty₂) ∧ (↥ctx)[0 ↦ ty₁] ⊢ t ⋮ ty₂
  | .abs h => ⟨_, rfl, h⟩  

theorem inversion_app : 
    (ctx ⊢ .app t₁ t₂ ⋮ ty₂) → ∃ ty₁, (ctx ⊢ t₁ ⋮ .arrow ty₁ ty₂) ∧ (ctx ⊢ t₂ ⋮ ty₁)
  | .app h₁ h₂ => ⟨_, h₁, h₂⟩

theorem uniqueness (h₁ : ctx ⊢ t ⋮ ty₁) (h₂ : ctx ⊢ t ⋮ ty₂) : ty₁ = ty₂ := by
  induction h₁ generalizing ty₂ <;> cases h₂
  case var.var h₁ h₂      => injection h₁ ▸ h₂
  case abs.abs hi _ h     => rw [hi h]
  case app.app hi _ _ _ h => injection hi h

theorem canonical_forms {v : Value} (h : ⊢ v ⋮ .arrow ty₁ ty₂) : ∃ t, v = .abs ty₁ t := by
  cases v
  case abs body =>
    simp at h
    exists body
    have ⟨_, h, _⟩ := inversion_abs h
    injection h with h
    rw [h]

theorem progress (h : ⊢ t ⋮ ty) : (∃ v : Value, t = v) ∨ (∃ t', t ⇒ t') := by
  generalize hc : (∅ : Ctx) = ctx
  rw [hc] at h
  induction h <;> (subst hc; simp at *)
  case var h => injection h
  case abs ty₁ t₁ _ _ _ => exact .inl ⟨⟨_, _⟩, rfl, rfl⟩
  case app hi₁ hi₂ =>
    cases hi₁ <;> apply Or.inr
    case inr h =>
      have ⟨_, h⟩ := h
      exact ⟨_, .app₁ _ h⟩
    case inl ty₁ _ _ ht₁ _ h₁ =>
      cases hi₂ 
      case inl h₂ =>
        have ⟨v₁, hv₁⟩ := h₁ 
        have ⟨v₂, hv₂⟩ := h₂
        subst hv₁ hv₂
        have ⟨body₁, hv₁⟩ := canonical_forms ht₁
        subst hv₁
        exact ⟨_, .beta ..⟩ 
      case inr h₂ =>
        have ⟨_, h₁⟩ := h₁
        have ⟨_, h₂⟩ := h₂
        subst h₁
        exact ⟨_, .app₂ _ h₂⟩
  
theorem Ctx.shift_zero : ↥ctx 0 = none := 
  rfl

theorem Ctx.shift_succ (ctx x) : ↥ctx (x + 1) = ctx x := 
  rfl

theorem Ctx.set_get_ne (ctx x y) (h : x ≠ y := by intro; contradiction) : 
    ctx[x ↦ ty] y = ctx y := by
  simp [set, h.symm]

theorem Ctx.set_ne_comm (ctx : Ctx) (x₁ x₂) (h : x₁ ≠ x₂ := by intro; contradiction) : 
    ctx[x₁ ↦ ty₁][x₂ ↦ ty₂] = ctx[x₂ ↦ ty₂][x₁ ↦ ty₁] := by
  funext
  simp [set]
  split <;> split <;> simp_all

theorem Ctx.shift_set_comm (ctx : Ctx) (x : Nat) : (↥ctx)[x + 1 ↦ ty] = ↥(ctx[x ↦ ty]) := by 
  funext
  simp [shift, set]
  split
  · simp [*]
  · split <;> simp_all

theorem weakening (ht : ctx ⊢ t ⋮ ty) (hx : ctx x = none) : ctx[x ↦ ty'] ⊢ t ⋮ ty := by
  induction ht generalizing x
  case var ctx _ y hy => 
    refine .var (hy ▸ ctx.set_get_ne _ _ ?_)
    intro h
    injection (h ▸ hx) ▸ hy
  case abs ctx _ _ _ hi =>
    specialize hi <| (hx ▸ ctx.shift_succ x) ▸ (↥ctx).set_get_ne 0 (x + 1)
    rw [(↥ctx).set_ne_comm 0 (x + 1), ctx.shift_set_comm x] at hi
    exact .abs hi
  case app hi₁ hi₂ => exact .app (hi₁ hx) (hi₂ hx)

-- TODO: These theorms might not be provable due to off-by-1 bugs.

theorem shift_up_preservation (h : ctx ⊢ t ⋮ ty) : ↥ctx ⊢ ↥t ⋮ ty := by
  induction h
  case var h => exact .var h
  case abs ty₁ ctx t ty₂ ht hi =>
    refine .abs ?_
    rw [←Ctx.shift_set_comm] at hi
    simp at *
    sorry
  case app hi₁ hi₂ => exact .app hi₁ hi₂

theorem shift_down_preservation (h : ↥ctx ⊢ t ⋮ ty) : ctx ⊢ ↧t ⋮ ty := by
  generalize hc : ↥ctx = ctx'
  rw [hc] at h
  induction h <;> (subst hc; try simp at *)
  case var h =>
    simp_all [Term.shift, Ctx.shift, Dir.move]
    split <;> try split at h <;> try contradiction
    exact .var h
  case abs => 
    sorry
  case app hi₁ hi₂ => exact .app hi₁ hi₂

theorem subst_preservation 
    (ht : ctx[x ↦ ty'] ⊢ t ⋮ ty) (hs : ctx ⊢ s ⋮ ty') : ctx ⊢ t[x ↦ s] ⋮ ty := by
  generalize hc : ctx[x ↦ ty'] = ctx'
  rw [hc] at ht
  induction ht generalizing ctx x s <;> (subst hc; try simp at *)
  case var hc =>
    simp [Term.subst]
    split <;> simp [Ctx.set] at hc
    case inl h => simp_all
    case inr h => exact .var <| by simp_all
  case abs ty₁ _ _ _ hi =>
    refine Types.abs <| hi ?_ ?_
    · exact weakening (shift_up_preservation hs) Ctx.shift_zero
    · rw [←ctx.shift_set_comm, (↥ctx).set_ne_comm 0 (x + 1)]
  case app hi₁ hi₂ => exact .app (hi₁ hs rfl) (hi₂ hs rfl)

theorem preservation (ht : ctx ⊢ t ⋮ ty) (he : t ⇒ t') : ctx ⊢ t' ⋮ ty := by
  induction ht generalizing t' <;> cases he
  case app.app₁ _ ht hi _ _ he => exact .app (hi he) ht
  case app.app₂ hi _ _ ht _ he => exact .app ht (hi he)
  case app.beta ht₁ _ ht₂ _ => 
    simp at * 
    have ⟨_, h, hc⟩ := inversion_abs ht₁
    injection h with h₁ h₂
    subst h₁ h₂
    exact shift_down_preservation <| subst_preservation hc (shift_up_preservation ht₂)

def NormalForm (t : Term) :=
  ¬∃ t', t ⇒ t'

inductive Eval.RTC : Term → Term → Prop
  | refl (t : Term) : Eval.RTC t t
  | trans : (t₁ ⇒ t₂) → Eval.RTC t₂ t₃ → Eval.RTC t₁ t₃

infixr:50 " ⇒* " => Eval.RTC

-- Note: This is also called "t halts" in Types and Programming Languages.
inductive Normalizable (t : Term) : Prop where
  | intro (eval : t ⇒* t') (nf : NormalForm t₁)

-- TODO:
--
-- inductive Saturated : Ty → Term → Prop
--   | arrow : Normalizable t → (∀ s, Saturated ty₁ s → Saturated ty₂ (.app t s)) → Saturated (.arrow ty₁ ty₂) t
-- 
-- theorem normalization (h : ⊢ t ⋮ ty) : Normalizable t :=
--   sorry

def type (ctx : Ctx) : Term → Option Ty
  | .var x     => ctx x
  | .abs ty t  => return .arrow ty (← type (↥ctx)[0 ↦ ty] t) 
  | .app t₁ t₂ => do
    let some (.arrow ty₁ ty₂) := type ctx t₁ | none
    if ty₁ = (← type ctx t₂) then ty₂ else none

theorem type_correct : (type ctx t = some ty) ↔ (ctx ⊢ t ⋮ ty) where
  mp h := by
    induction t generalizing ty ctx <;> simp [type, bind, Option.bind] at h
    case var => exact .var h
    case abs hi => 
      split at h <;> try contradiction
      case _ ht =>
        simp [pure] at h
        subst h
        exact .abs (hi ht)
    case app t₁ t₂ hi₁ hi₂ =>
      cases h₁ : type ctx t₁ <;> cases h₂ : type ctx t₂ <;> simp_all [h₁, h₂]
      all_goals split at h <;> try contradiction
      case _ ty₁ ty₂ _ ty₁₁ _ ha =>
        specialize hi₁ h₁
        split at h <;> simp_all
        exact .app hi₁ (hi₂ h₂)       
  mpr h := by
    induction h <;> simp [type]
    case var         => assumption
    case abs hi      => rw [hi]; rfl
    case app hi₁ hi₂ => simp [hi₁, hi₂]; exact if_pos rfl

      