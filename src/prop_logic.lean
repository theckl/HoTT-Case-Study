import hott.init hott.types.trunc

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open is_trunc trunc equiv hott.is_equiv

/- We define [True] and [False] as (bundled) propositions. -/
@[hott]
inductive true : Type u
| intro : true

@[hott]
def eq_true : forall t₁ t₂ : true, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl true.intro),
end 

@[hott, instance]
def is_prop_true : is_prop true :=
  is_prop.mk eq_true 

@[hott]
def True : Prop :=
  Prop.mk true is_prop_true  

@[hott]
inductive false : Type u

@[hott]
def eq_false : forall f₁ f₂ : false, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance]
def is_prop_false : is_prop false :=
  is_prop.mk eq_false

@[hott]
def False : Prop :=
  Prop.mk false is_prop_false

/- Inhabited [Prop]s over equalities have pathover. -/
@[hott]
def pathover_prop_eq {A : Type.{u}} (P : A -> trunctype.{u} -1) {a₁ a₂ : A} (e : a₁ = a₂) :
  ∀ (p₁ : P a₁) (p₂ : P a₂), p₁ =[e; λ a : A, P a] p₂ :=
assume p₁ p₂, concato_eq (pathover_tr e p₁) (is_prop.elim (e ▸ p₁) p₂)   

/- Logically equivalent mere propositions are equivalent. -/
@[hott]
def is_prop_iff_equiv : 
  Π {A B : Type.{u}} [is_prop A] [is_prop B], (A ↔ B) -> (A ≃ B) :=
assume A B pA pB AiffB,
let AB := AiffB.1, BA := AiffB.2 in
have rinv : Π b : B, AB (BA b) = b, from assume b, @is_prop.elim B pB _ _,
have linv : Π a : A, BA (AB a) = a, from assume a, @is_prop.elim A pA _ _,
equiv.mk AB (adjointify AB BA rinv linv)

/- Inhabited mere propositions are equal. The proof needs univalence. -/
@[hott]
def inhabited_prop_eq (A B : Type u) [is_prop A] [is_prop B] (a : A) (b : B) : 
  A = B :=
have AeqvB : A ≃ B, from is_prop_iff_equiv ((λ a : A, b), (λ b : B, a)),
ua AeqvB   

/- Inhabited mere propostions in a type family over equal base points are
   pathover-equal. -/
@[hott]
def inhabited_prop_po {A : Type u} (P Q : Type u) {a b : A} (eq : a = b) 
  [is_prop P] [is_prop Q] (p : P) (q : Q): 
  P =[eq; λ a : A, Type u] Q :=
have prop_eq : P = Q, from inhabited_prop_eq P Q p q, 
pathover_of_eq eq prop_eq  

end hott