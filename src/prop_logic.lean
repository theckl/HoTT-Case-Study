import hott.init hott.types.trunc hott.types.prod

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open is_trunc trunc equiv hott.is_equiv hott.prod

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

/- [and] and [iff] produce propositions from propositions. -/
@[hott, instance]
def and_is_prop (A B : Type u) [is_prop A] [is_prop B] : is_prop (A × B) :=
  have eq_and : ∀ c₁ c₂ : A × B, c₁ = c₂, from 
    begin
      intros c₁ c₂, 
      hinduction c₁ with a₁ b₁, hinduction c₂ with a₂ b₂, 
      apply pair_eq, apply is_prop.elim, apply is_prop.elim,
    end,
  is_prop.mk eq_and 

@[hott]
lemma is_prop_map {A B : Type u} (pB : is_prop B) : is_prop (A -> B) :=
have eq_map : forall f1 f2 : A -> B, f1 = f2, from 
  assume f1 f2, 
  have map_hom : f1 ~ f2, from 
    assume a, is_prop.elim _ _, 
  eq_of_homotopy map_hom,
is_prop.mk eq_map 

@[hott]
lemma is_prop_dprod {A : Type u} {P : A -> Type u} 
    (pP : forall a : A, is_prop (P a)) : 
  is_prop (forall a : A, P a) :=
have eq_prod : forall dP1 dP2 : (forall a : A, P a), dP1 = dP2, from 
  assume dP1 dP2, 
  have dP_hom : dP1 ~ dP2, from 
    assume a, 
    is_prop.elim _ _, 
  eq_of_homotopy dP_hom,
is_prop.mk eq_prod  

@[hott, instance]
def iff_is_prop (A B : Type u) [pA : is_prop A] [pB : is_prop B] : is_prop (A ↔ B) :=
  @and_is_prop (A -> B) (B -> A) (is_prop_map pB) (is_prop_map pA)  

@[hott, instance]
def prop_equiv_is_prop (A B : Type u) [pA : is_prop A] [pB : is_prop B] : is_prop (A ≃ B) :=
sorry

/- Inhabited [Prop]s over equalities have pathover. -/
@[hott]
def pathover_prop_eq {A : Type.{u}} (P : A -> trunctype.{u} -1) {a₁ a₂ : A} (e : a₁ = a₂) :
  ∀ (p₁ : P a₁) (p₂ : P a₂), p₁ =[e; λ a : A, P a] p₂ :=
assume p₁ p₂, concato_eq (pathover_tr e p₁) (is_prop.elim (e ▸ p₁) p₂)   

/- Logically equivalent mere propositions are equivalent. -/
@[hott]
def prop_iff_equiv : 
  Π {A B : Type.{u}} [is_prop A] [is_prop B], (A ↔ B) -> (A ≃ B) :=
assume A B pA pB AiffB,
let AB := AiffB.1, BA := AiffB.2 in
have rinv : Π b : B, AB (BA b) = b, from assume b, @is_prop.elim B pB _ _,
have linv : Π a : A, BA (AB a) = a, from assume a, @is_prop.elim A pA _ _,
equiv.mk AB (adjointify AB BA rinv linv)

@[hott]
lemma prop_iff_eq : Π {A B : Prop} (imp1 : A -> B) (imp2 : B -> A), A = B 
| (trunctype.mk carA structA) (trunctype.mk carB structB) :=
  assume imp1 imp2, 
  have car_eqv : carA ≃ carB, from @prop_iff_equiv _ _ structA structB (imp1, imp2),
  have car_eq : carA = carB, from ua car_eqv, /- Do you really need univalence here? -/
  have struct_tr : car_eq ▸ structA = structB, from 
    is_prop.elim _ _,
  have struct_eq : structA =[car_eq] structB, from pathover_of_tr_eq struct_tr,
  apd011 Prop.mk car_eq struct_eq

@[hott]
def prop_iff_eqv_eq :
  Π (A B : Type.{u}) [is_prop A] [is_prop B], (A ↔ B) ≃ (A = B) :=
assume A B pA pB,
have prop_eqv_equiv_eqv : (A ↔ B) ≃ (A ≃ B), from  
  let f := @prop_iff_equiv A B pA pB in
  let g := λ eqv : A ≃ B, (eqv.to_fun, eqv⁻¹ᶠ) in
  have rinv : ∀ eqv : A ≃ B, f (g eqv) = eqv, from sorry,
  have linv : ∀ peqv : A ↔ B, g (f peqv) = peqv, from 
    assume peqv, @is_prop.elim _ (@iff_is_prop A B pA pB) _ _,
  equiv.mk f (adjointify f g rinv linv),
equiv.trans prop_eqv_equiv_eqv (equiv.symm (eq_equiv_equiv A B))   

/- Equality of proposition is a mere proposition. -/
@[hott, instance]
def eq_prop_is_prop (P Q : Type u) [is_prop P] [is_prop Q] : is_prop (P = Q) :=
  is_trunc_is_equiv_closed -1 (@prop_iff_eqv_eq P Q _ _) (@iff_is_prop P Q _ _) 

/- Inhabited mere propositions are equal. The proof needs univalence. -/
@[hott]
def inhabited_prop_eq (A B : Type u) [is_prop A] [is_prop B] (a : A) (b : B) : 
  A = B :=
have AeqvB : A ≃ B, from prop_iff_equiv ((λ a : A, b), (λ b : B, a)),
ua AeqvB   

/- Inhabited mere propositions in a type family over equal base points are
   pathover-equal. -/
@[hott]
def inhabited_prop_po {A : Type u} (P Q : Type u) {a b : A} (eq : a = b) 
  [is_prop P] [is_prop Q] (p : P) (q : Q) : 
  P =[eq; λ a : A, Type u] Q :=
have prop_eq : P = Q, from inhabited_prop_eq P Q p q, 
pathover_of_eq eq prop_eq  

/- Transported propositions are propositions. -/
@[hott, instance]
def tr_prop_prop {A : Type u} {a₁ a₂ : A} (e : a₁ = a₂) 
  (P : Type u) [is_prop P] : is_prop (e ▸ P) :=
begin 
  hinduction e, hsimp, assumption,
end  

/- Pathover equalities of propositions are propositions. -/
@[hott, instance]
def po_is_prop {A : Type u} {P Q : Type u} {a b : A} (eq : a = b) 
  [is_prop P] [is_prop Q] : is_prop (P =[eq; λ a : A, Type u] Q) :=
have tr_prop : is_prop (eq ▸ P = Q), from 
  @eq_prop_is_prop (eq ▸ P) Q (tr_prop_prop eq P) _,
is_trunc_is_equiv_closed_rev -1 (pathover_equiv_tr_eq eq P Q) tr_prop

end hott