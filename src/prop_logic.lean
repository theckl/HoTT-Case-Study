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

/- The next lemmas and constructions are all needed to show that an equivalence of 
   propositions is a proposition. The proof requires lots of equalities of structures,
   hence applications of their constructors to dependent equalities. These applications
   should be automatically generated and shown for every structure. -/
@[hott]
def po_proofs {A : Type u} {a₁ a₂ : A} (e : a₁ = a₂) {B : A -> Type v}  
  [pBa₂ : is_prop (B a₂)] (b₁ : B a₁) (b₂ : B a₂) :
  b₁ =[e] b₂ :=
have tr_B : e ▸ b₁ = b₂, from @is_prop.elim _ pBa₂ _ _,
pathover_of_tr_eq tr_B  

@[hott]
def adj_eq {A B : Type u} (f₁ f₂ : A -> B) (g₁ g₂ : B -> A) 
  (rinv₁ : ∀ b : B, f₁ (g₁ b) = b) (rinv₂ : ∀ b : B, f₂ (g₂ b) = b)  
  (linv₁ : ∀ a : A, g₁ (f₁ a) = a) (linv₂ : ∀ a : A, g₂ (f₂ a) = a)
  (Hf : f₁ = f₂) (Hg : g₁ = g₂) 
  (Hr : rinv₁ =[apd011 _ Hf (pathover_of_eq Hf Hg); id] rinv₂)
  (Hl : linv₁ =[apd011 _ Hf (pathover_of_eq Hf Hg); id] linv₂) : 
adjointify f₁ g₁ rinv₁ linv₁ =[Hf] adjointify f₂ g₂ rinv₂ linv₂ :=
begin hinduction Hf, hinduction Hg, hinduction Hr, hinduction Hl, refl end  

@[hott]
def inv_is_prop {A B : Type u} [is_prop A] (f : A -> B) (g : B -> A) : 
  is_prop (∀ a : A, g (f a) = a) :=
is_prop_dprod (λ a : A, @is_trunc_succ _ -2 (is_trunc_eq -2 _ _))

@[hott]
def is_equiv_mk_adj {A B : Type u} [is_prop A] [is_prop B] (f : A -> B) (g : B -> A) 
  (rinv : ∀ b : B, f (g b) = b) (linv : ∀ a : A, g (f a) = a) 
  (adj : Π a, rinv (f a) = ap f (linv a)) :
is_equiv.mk' g rinv linv adj = adjointify f g rinv linv :=
  let adj_linv := adjointify_left_inv' f g rinv linv,
      adj' := adjointify_adj' f g rinv linv in
  have adj'_is_prop : is_prop (Π a, rinv (f a) = ap f (adj_linv a)), from 
    have rfa_is_prop : ∀ a : A, is_prop (f (g (f a)) = f a), from 
      assume a, @is_trunc_succ _ -2 (is_trunc_eq -2 _ _),
    is_prop_dprod (λ a : A, @is_trunc_succ _ -2 (is_trunc_eq -2 _ _)),
  have Hlinv : linv = adj_linv, from @is_prop.elim _ (inv_is_prop f g) _ _,
  have Hadj : adj =[Hlinv; λ l : (∀ a, g (f a) = a), Π a, rinv (f a) = ap f (l a)] adj', from 
    @po_proofs _ _ _ Hlinv (λ l, Π a, rinv (f a) = ap f (l a)) adj'_is_prop _ _,
  calc is_equiv.mk' g rinv linv adj = is_equiv.mk' g rinv adj_linv adj' :
       apd011 _ Hlinv Hadj
       ... = adjointify f g rinv linv : rfl

@[hott]
def prop_is_equiv_is_prop {A B : Type u} [pA : is_prop A] [pB : is_prop B] 
  (f₁ f₂ : A -> B) (ef : f₁ = f₂) : 
Π (is_eqv₁ : is_equiv f₁) (is_eqv₂ : is_equiv f₂), is_eqv₁ =[ef] is_eqv₂ 
| (is_equiv.mk' g₁ rinv₁ linv₁ adj₁) (is_equiv.mk' g₂ rinv₂ linv₂ adj₂) :=
have eg : g₁ = g₂, from 
  have pAB : is_prop (B -> A), from is_prop_map pA,
  @is_prop.elim _ pAB _ _, 
have er : rinv₁ =[apd011 _ ef (pathover_of_eq ef eg); id] rinv₂, from 
  begin apply pathover_of_tr_eq, exact @is_prop.elim _ (inv_is_prop g₂ f₂) _ _ end,
have el : linv₁ =[apd011 _ ef (pathover_of_eq ef eg); id] linv₂, from 
  begin apply pathover_of_tr_eq, exact @is_prop.elim _ (inv_is_prop f₂ g₂) _ _ end,  
eq_concato (is_equiv_mk_adj f₁ g₁ rinv₁ linv₁ adj₁) 
           (concato_eq (adj_eq f₁ f₂ g₁ g₂ rinv₁ rinv₂ linv₁ linv₂ ef eg er el)
           (is_equiv_mk_adj f₂ g₂ rinv₂ linv₂ adj₂)⁻¹)

@[hott, instance]
def prop_equiv_is_prop (A B : Type u) [pA : is_prop A] [pB : is_prop B] : is_prop (A ≃ B) :=
have eq_equiv : ∀ eqv₁ eqv₂ : A ≃ B, eqv₁ = eqv₂, from assume eqv₁ eqv₂,    
  have eqv_eq : eqv₁.to_fun = eqv₂.to_fun, from 
    have pAB : is_prop (A -> B), from is_prop_map pB,
    @is_prop.elim _ pAB _ _,
  have is_equiv_eq : eqv₁.to_is_equiv =[eqv_eq] eqv₂.to_is_equiv, from 
    prop_is_equiv_is_prop _ _ eqv_eq _ _, 
  begin 
    hinduction eqv₁, hinduction eqv₂,    
    exact apd011 equiv.mk eqv_eq is_equiv_eq,
  end,
is_prop.mk eq_equiv

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
def prop_iff_eqv_equiv :
  Π (A B : Type.{u}) [is_prop A] [is_prop B], (A ↔ B) ≃ (A ≃ B) :=
assume A B pA pB,
let f := @prop_iff_equiv A B pA pB in
let g := λ eqv : A ≃ B, (eqv.to_fun, eqv⁻¹ᶠ) in
have rinv : ∀ eqv : A ≃ B, f (g eqv) = eqv, from assume eqv,
  @is_prop.elim (A ≃ B) (@prop_equiv_is_prop _ _ pA pB) _ _,
have linv : ∀ peqv : A ↔ B, g (f peqv) = peqv, from 
  assume peqv, @is_prop.elim _ (@iff_is_prop A B pA pB) _ _,
equiv.mk f (adjointify f g rinv linv)

@[hott]
def prop_iff_eqv_eq :
  Π (A B : Type.{u}) [is_prop A] [is_prop B], (A ↔ B) ≃ (A = B) :=
assume A B pA pB,
equiv.trans (@prop_iff_eqv_equiv A B pA pB) (equiv.symm (eq_equiv_equiv A B))   

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

/- The Law of Excluded Middle of a proposition is a proposition. 
   Should be in [types.sum] but even if so this file cannot be imported: 
   [invalid import: hott.types.sum
    invalid object declaration, environment already has an object named 'sum.rec._ind_info'] -/
@[hott]
def is_prop_LEM {A : Type u} [is_prop A] : is_prop (A ⊎ ¬ A) :=
  have eq_sum : ∀ x y : A ⊎ ¬ A, x = y, from 
  begin
    intros x y,
    hinduction x with a na,
      hinduction y with a' na', 
        apply ap, apply is_prop.elim,
        apply empty.elim, exact na' a,
      hinduction y with a' na',
        apply empty.elim, exact na a',
        apply ap, apply is_prop.elim,  
  end,
  is_prop.mk eq_sum    

end hott