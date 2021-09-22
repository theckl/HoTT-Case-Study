import hott.init hott.types.trunc hott.types.prod init2

universes u v w
hott_theory

namespace hott
open is_trunc trunc equiv hott.is_equiv hott.prod

set_option pp.universes true

/- Nicer name for construction of `Prop` from `is_prop`. -/
@[hott]
def to_Prop (A : Type u) [pA : is_prop A] : trunctype -1 :=
  trunctype.mk A pA 

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

@[hott]
def False_uninhabited : ¬ False := 
  begin intro false, hinduction false end  

/- Some instances of propositions. -/
@[hott, instance]
lemma is_prop_map {A B : Type _} (pB : is_prop B) : is_prop (A -> B) :=
have eq_map : forall f1 f2 : A -> B, f1 = f2, from 
  assume f1 f2, 
  have map_hom : f1 ~ f2, from 
    assume a, is_prop.elim _ _, 
  eq_of_homotopy map_hom,
is_prop.mk eq_map 

@[hott, instance]
lemma is_prop_dprod {A : Type u} {P : A -> Type v} 
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
lemma is_prop_dprod2 {A : Type u} {P : A -> A -> Type v} 
    (pP : forall a b : A, is_prop (P a b)) : 
  is_prop (forall a b : A, P a b) :=
have eq_prod : forall dP1 dP2 : (forall a b : A, P a b), dP1 = dP2, from 
  assume dP1 dP2, 
  have dP_hom : dP1 ~ dP2, from 
    assume a, 
    is_prop.elim _ _, 
  eq_of_homotopy dP_hom,
is_prop.mk eq_prod

@[hott, instance]
def iff_is_prop (A B : Type _) [pA : is_prop A] [pB : is_prop B] : is_prop (A ↔ B) :=
  @prod.is_trunc_prod (A -> B) (B -> A) -1 (is_prop_map pB) (is_prop_map pA)  

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
def adj_eq {A B : Type _} (f₁ f₂ : A -> B) (g₁ g₂ : B -> A) 
  (rinv₁ : ∀ b : B, f₁ (g₁ b) = b) (rinv₂ : ∀ b : B, f₂ (g₂ b) = b)  
  (linv₁ : ∀ a : A, g₁ (f₁ a) = a) (linv₂ : ∀ a : A, g₂ (f₂ a) = a)
  (Hf : f₁ = f₂) (Hg : g₁ = g₂) 
  (Hr : rinv₁ =[apd011 _ Hf (pathover_of_eq Hf Hg); id] rinv₂)
  (Hl : linv₁ =[apd011 _ Hf (pathover_of_eq Hf Hg); id] linv₂) : 
adjointify f₁ g₁ rinv₁ linv₁ =[Hf] adjointify f₂ g₂ rinv₂ linv₂ :=
begin hinduction Hf, hinduction Hg, hinduction Hr, hinduction Hl, refl end  

@[hott]
def inv_is_prop {A B : Type _} [is_prop A] (f : A -> B) (g : B -> A) : 
  is_prop (∀ a : A, g (f a) = a) :=
is_prop_dprod (λ a : A, @is_trunc_succ _ -2 (is_trunc_eq -2 _ _))

@[hott]
def is_equiv_mk_adj {A B : Type _} [is_prop A] [is_prop B] (f : A -> B) (g : B -> A) 
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
def prop_is_equiv_is_prop {A B : Type _} [pA : is_prop A] [pB : is_prop B] 
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
def prop_equiv_is_prop (A B : Type _) [pA : is_prop A] [pB : is_prop B] : is_prop (A ≃ B) :=
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
def pathover_prop_eq {A : Type _} (P : A -> trunctype -1) {a₁ a₂ : A} (e : a₁ = a₂) :
  ∀ (p₁ : P a₁) (p₂ : P a₂), p₁ =[e; λ a : A, P a] p₂ :=
assume p₁ p₂, concato_eq (pathover_tr e p₁) (is_prop.elim (e ▸ p₁) p₂)   

/- Logically equivalent mere propositions are equivalent. -/
@[hott]
def prop_iff_equiv : 
  Π {A B : Type u} [is_prop A] [is_prop B], (A ↔ B) -> (A ≃ B) :=
assume A B pA pB AiffB,
let AB := AiffB.1, BA := AiffB.2 in
have rinv : Π b : B, AB (BA b) = b, from assume b, @is_prop.elim B pB _ _,
have linv : Π a : A, BA (AB a) = a, from assume a, @is_prop.elim A pA _ _,
equiv.mk AB (adjointify AB BA rinv linv)

@[hott]
lemma prop_iff_eq : Π {A B : trunctype -1} (imp1 : A -> B) (imp2 : B -> A), 
  A = B 
| (trunctype.mk carA structA) (trunctype.mk carB structB) :=
  assume imp1 imp2, 
  have car_eqv : carA ≃ carB, from @prop_iff_equiv _ _ structA structB 
                                                                 (imp1, imp2),
  have car_eq : carA = carB, from ua car_eqv, 
  -- Do you really need univalence here? Requires `A` and `B` to be in the same universe.  
  have struct_tr : car_eq ▸ structA = structB, from 
    is_prop.elim _ _,
  have struct_eq : structA =[car_eq] structB, from pathover_of_tr_eq struct_tr,
  apd011 Prop.mk car_eq struct_eq

@[hott]
def prop_iff_eqv_equiv :
  Π (A B : Type _) [is_prop A] [is_prop B], (A ↔ B) ≃ (A ≃ B) :=
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
  Π (A B : Type _) [is_prop A] [is_prop B], (A ↔ B) ≃ (A = B) :=
assume A B pA pB,
equiv.trans (@prop_iff_eqv_equiv A B pA pB) (equiv.symm (eq_equiv_equiv A B))   

@[hott]
def inhab_props_iff {P Q : Prop} (p : P) (q : Q) : P ↔ Q :=
begin fapply pair, intro p, exact q, intro q, exact p end

/- Interchanging between types that are proposition and `Prop` -/
@[hott]
def to_Prop_eq (P : Prop) : to_Prop ↥P = P :=
  have to_Prop_iff : to_Prop ↥P <-> P, from 
    begin
      apply pair,
      { intro tP, assumption }, 
      { intro P, assumption }
    end,
  prop_iff_eq to_Prop_iff.1 to_Prop_iff.2

/- Equality of proposition is a mere proposition. -/
@[hott, instance]
def eq_prop_is_prop (P Q : Type _) [is_prop P] [is_prop Q] : is_prop (P = Q) :=
  is_trunc_is_equiv_closed -1 (@prop_iff_eqv_eq P Q _ _) (@iff_is_prop P Q _ _) 

/- Inhabited and unhabited mere propositions are equal. -/
@[hott]
def inhabited_Prop_eq (A B : trunctype -1) (a : A) (b : B) : 
  A = B :=
have A_imp_B : A -> B, from 
  assume a', b,
have B_imp_A : B -> A, from 
  assume b', a,
prop_iff_eq A_imp_B B_imp_A

@[hott]
def inhabited_prop_eq (A B : Type _) [pA : is_prop A] [pB : is_prop B] (a : A) (b : B) : 
  A = B :=
let Prop_A := trunctype.mk A pA,
    Prop_B := trunctype.mk B pB in
have Prop_eq : Prop_A = Prop_B, from inhabited_Prop_eq Prop_A Prop_B a b, 
ap trunctype.carrier Prop_eq 

@[hott]
def uninhabited_Prop_eq (A B : trunctype -1) (na : ¬ A) (nb : ¬ B) : 
  A = B :=
have A_imp_B : A -> B, from 
  assume a, by hinduction (na a),
have B_imp_A : B -> A, from 
  assume b, by hinduction (nb b),
prop_iff_eq A_imp_B B_imp_A

/- Inhabited mere propositions in a type family over equal base points are
   pathover-equal. -/
@[hott]
def inhabited_prop_po {A : Type _} (P Q : Type _) {a b : A} (eq : a = b) 
  [is_prop P] [is_prop Q] (p : P) (q : Q) : 
  P =[eq; λ a : A, Type _] Q :=
have prop_eq : P = Q, from inhabited_prop_eq P Q p q, 
pathover_of_eq eq prop_eq  

/- Transported propositions are propositions. -/
@[hott, instance]
def tr_prop_prop {A : Type _} {a₁ a₂ : A} (e : a₁ = a₂) 
  (P : Type u) [is_prop P] : is_prop (e ▸ P) :=
begin 
  hinduction e, hsimp, assumption,
end  

/- Pathover equalities of propositions are propositions. -/
@[hott, instance]
def po_is_prop {A : Type _} {P Q : Type _} {a b : A} (eq : a = b) 
  [is_prop P] [is_prop Q] : is_prop (P =[eq; λ a : A, Type _] Q) :=
have tr_prop : is_prop (eq ▸ P = Q), from 
  @eq_prop_is_prop (eq ▸ P) Q (tr_prop_prop eq P) _,
is_trunc_is_equiv_closed_rev -1 (pathover_equiv_tr_eq eq P Q) tr_prop

/- We introduce the universe lift of propositions as a special case of the lift of trunctypes. -/
@[hott]
def prop_ulift : trunctype.{u} -1 -> trunctype.{max v u} -1 := @trunctype_ulift -1

@[hott]
def prop_ulift_inv (P : Prop) : prop_ulift P -> P :=
  @ulift_equiv ↥P 

/- We do Classical Logic. Note that LEM follows form the Axiom of Choice, by
   Diaconescu's Theorem (see [set_axioms]).
   
   The Law of the Excluded Middle, following the HoTT-book, (3.4.1) -/
@[hott]   
def ExcludedMiddle := Π (A : Prop), A ⊎ ¬ A

/- The Law of Excluded Middle of a proposition is a proposition. 
   Should be in [types.sum] but even if so this file cannot be imported: 
   [invalid import: hott.types.sum
    invalid object declaration, environment already has an object named 'sum.rec._ind_info'] -/
@[hott]
def is_prop_LEM {A : Type _} [is_prop A] : is_prop (A ⊎ ¬ A) :=
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

@[hott]
axiom LEM : ExcludedMiddle

@[hott]  
def PropResize := trunctype.{max u v} -1 -> trunctype.{u} -1 

@[hott]
axiom PRES : PropResize  

/- The next lemma is needed for deducing propositional resizing from LEM. -/
@[hott]
def LEM_resize : ExcludedMiddle.{max u v} -> ExcludedMiddle.{u} :=
  assume LEM_u1 A,
  have LEM_u1_type : Π (B : Type (max u v)), is_prop B -> B ⊎ ¬ B, from 
    assume B B_is_prop, let Prop_B := trunctype.mk B B_is_prop in
    LEM_u1 Prop_B,
  have LEM_u1_A : (ulift.{max u v} A) ⊎ ¬ (ulift.{max u v} A), from 
    LEM_u1_type (ulift.{max u v} A) (prop_ulift A).struct, 
  begin
    hinduction LEM_u1_A with a_u1 not_a_u1,
      exact sum.inl a_u1.down,
      exact sum.inr (λ a : A, not_a_u1 (ulift.up a))
  end 

/- We need a set-type `Two` with two objects to deduce propositional resizing from LEM.
   To construct it we also need `Zero` and `One`. 

   [Zero] and [One] are equivalent to [true] and [false] in [prop_logic], but
   we want to use them without logical connotations. -/
@[hott]
inductive Zero : Type _

@[hott]
def eq_Zero : forall f₁ f₂ : Zero, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance]
def Zero_is_prop : is_prop Zero :=
  is_prop.mk eq_Zero 

@[hott]
def Zero_Set : Set :=
  Set.mk Zero (is_trunc_succ Zero -1)

@[hott]
inductive One : Type _  
| star : One

@[hott]
def eq_One : forall t₁ t₂ : One, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl One.star),
end 

@[hott, instance]
def One_is_prop : is_prop One :=
  is_prop.mk eq_One

@[hott]
def One_Set : Set :=
  Set.mk One (is_trunc_succ One -1)

@[hott]
inductive Two : Type _ 
| zero : Two 
| one : Two 

/- We prove that [Two] is a set using the encode-decode method presented in the
   HoTT-book, Sec.2.13. -/
@[hott, hsimp]
def code_Two : Two.{u} -> Two.{u} -> Type u :=
begin
  intros t₁ t₂, 
  induction t₁,
    induction t₂, exact One, exact Zero,
    induction t₂, exact Zero, exact One,
end  

@[hott, hsimp]
def encode_Two : Π t₁ t₂ : Two, (t₁ = t₂) -> code_Two t₁ t₂ :=
  have r : Π t : Two, code_Two t t, by 
    intro t; induction t; exact One.star; exact One.star,
  assume t₁ t₂ eq, transport (λ t : Two, code_Two t₁ t) eq (r t₁)

@[hott, hsimp]
def decode_Two : Π t₁ t₂ : Two, code_Two t₁ t₂ -> (t₁ = t₂) :=
begin
  intros t₁ t₂,
  induction t₁, 
    induction t₂, intro; refl, intro f; induction f,
    induction t₂, intro f; induction f, intro; refl,     
end    

@[hott]
def Two_eq_equiv_code : ∀ t₁ t₂ : Two, (t₁ = t₂) ≃ code_Two t₁ t₂ := 
  assume t₁ t₂, 
  have z1 : code_Two Two.zero Two.one -> Zero, from λ c, c,
  have z2 : code_Two.{u} Two.one Two.zero -> Zero, from λ c, c,
  have rinv : ∀ c : code_Two t₁ t₂, (encode_Two t₁ t₂) (decode_Two t₁ t₂ c) = c, from
    assume c, 
    begin
      induction t₁, 
        induction t₂, induction c; refl, exact Zero.rec _ (z1 c),  
        induction t₂, exact Zero.rec _ (z1 c), induction c; refl, 
    end,  
  have linv : ∀ eq : t₁ = t₂, (decode_Two t₁ t₂) (encode_Two t₁ t₂ eq) = eq, from
    begin
      intro eq,
      induction eq,
      induction t₁, 
      refl, refl,
    end,    
  equiv.mk (encode_Two t₁ t₂) 
           (is_equiv.adjointify (encode_Two t₁ t₂) (decode_Two t₁ t₂) rinv linv)

@[hott, instance]
def Two_is_set : is_set Two.{u} :=
  have Two_eq_is_prop : ∀ t₁ t₂ : Two.{u}, is_prop (t₁ = t₂), from 
    assume t₁ t₂,
    have code_Two_is_prop : is_prop (code_Two t₁ t₂), from
      begin
        induction t₁, 
          induction t₂, exact One_is_prop, exact Zero_is_prop,
          induction t₂, exact Zero_is_prop, exact One_is_prop,
      end,
    is_trunc_equiv_closed_rev -1 (Two_eq_equiv_code t₁ t₂) code_Two_is_prop,
  is_trunc_succ_intro Two_eq_is_prop

@[hott]
def Two_Set : Set :=
  Set.mk Two Two_is_set  

@[hott]
def Two_is_decidable : ∀ t₁ t₂ : Two, (t₁ = t₂) ⊎ ¬ (t₁ = t₂) :=
begin 
  intros t₁ t₂, 
  induction t₁, 
    induction t₂, exact sum.inl rfl, 
                  apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
    induction t₂, apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
                  exact sum.inl rfl,              
end    

/- We need resizing of the universe in which [Two] lives, to show that LEM implies propositional
   resizing. -/
@[hott, hsimp]
def Two_lift : Two.{u} -> Two.{max u v} := 
begin  
  intro t,
  hinduction t, exact Two.zero, exact Two.one
end

@[hott, hsimp]
def Two_resize : Two.{max u v} -> Two.{u} := 
begin  
  intro t,
  hinduction t, exact Two.zero, exact Two.one
end

@[hott, reducible]
def Two_equiv_lift : Two.{u} ≃ Two.{max u v} :=
  have rinv : ∀ t : Two.{max u v}, Two_lift (Two_resize t) = t, by
      intro t; hinduction t; hsimp; hsimp, 
  have linv : ∀ t : Two.{u}, Two_resize (Two_lift t) = t, by
      intro t; hinduction t; hsimp; hsimp,      
  equiv.mk Two_lift (adjointify Two_lift Two_resize rinv linv)

/- This is Ex.3.9 in the HoTT-book. -/
@[hott, hsimp]
def LEM_Prop_Two : ExcludedMiddle.{u} -> trunctype.{u} -1 -> Two.{u} := 
  assume lem P, let lem_P := lem P in
  begin hinduction (lem_P) with p np, exact Two.one, exact Two.zero end

@[hott, hsimp]
def Two_Prop : Two.{u} -> trunctype.{u} -1 := 
  begin intro t, hinduction t, exact False, exact True end

@[hott]
def LEM_Prop_equiv_Two : ExcludedMiddle.{u} -> (trunctype.{u} -1 ≃ Two.{u}) :=
  assume lem,
  have rinv : ∀ t : Two.{u}, LEM_Prop_Two lem (Two_Prop t) = t, 
    begin 
      intro t, hinduction t, 
        change LEM_Prop_Two lem False = Two.zero,  
        hinduction (lem False) with F f nf,
          hinduction f,
          hsimp, rwr F,
        hinduction (lem True) with T t nt,
          hsimp, rwr T,
          hinduction (nt true.intro),  
    end,
  have linv : ∀ P : trunctype.{u} -1, Two_Prop (LEM_Prop_Two lem P) = P, from
    begin  
      intro P, 
      hinduction (lem P) with lem_P_eq p np,
        hsimp, rwr lem_P_eq, change True = P, apply inhabited_Prop_eq,
          exact true.intro, exact p,
        hsimp, rwr lem_P_eq, change False = P, apply uninhabited_Prop_eq,
          exact False_uninhabited, exact np 
    end, 
  equiv.mk (LEM_Prop_Two lem) (adjointify (LEM_Prop_Two lem) Two_Prop rinv linv)     

/- Propositional Resizing is a consequence of LEM in all universes [HoTT-Book, Ex.3.10]. 

   We compose the equivalences of [Prop] with [Two] in two successive universes and the 
   equivalence of [Two] with its lift to the next universe. -/
@[hott, reducible, hsimp]
def LEM_Prop_Resize : ExcludedMiddle.{max u v} -> (trunctype.{u} -1 ≃ trunctype.{max u v} -1) :=
  assume lem_u1,
  have lem_u : ExcludedMiddle.{u}, from LEM_resize lem_u1,
  equiv.trans (LEM_Prop_equiv_Two lem_u) 
              (equiv.trans (Two_equiv_lift.{u}) (equiv.symm (LEM_Prop_equiv_Two lem_u1)))

@[hott, reducible, hsimp]  
def prop_resize : trunctype.{max u v} -1 -> trunctype.{u} -1 := (LEM_Prop_Resize LEM)⁻¹ᶠ  

@[hott]
def prop_resize_trivial : ∀ (P : trunctype.{u} -1), prop_resize.{u u} P = P :=
begin 
  intro P, hsimp, hinduction LEM P with lem q nq, 
  { have eq : (LEM_Prop_equiv_Two LEM).to_fun P = Two.one, from
      begin change LEM_Prop_Two LEM P = Two.one, hsimp, rwr lem end,
    rwr eq, hsimp, change True = P, apply inhabited_Prop_eq, exact true.intro, exact q },
  { have eq : (LEM_Prop_equiv_Two LEM).to_fun P = Two.zero, from
      begin change LEM_Prop_Two LEM P = Two.zero, hsimp, rwr lem end,
    rwr eq, hsimp, change False = P, apply uninhabited_Prop_eq, 
    { intro F, hinduction F }, 
    { exact nq } } 
end 

@[hott, reducible, hsimp]
def prop_to_prop_resize {P : Prop} : P -> prop_resize P :=
begin 
  intro p, hsimp, 
  have eq : (LEM_Prop_equiv_Two LEM).to_fun P = Two.one, from 
    begin 
      change LEM_Prop_Two LEM P = Two.one, hsimp, hinduction LEM P with lem q nq, 
      { hsimp }, 
      { hinduction nq p }
    end,
  rwr eq, hsimp, exact true.intro 
end

@[hott, reducible, hsimp]
def prop_resize_to_prop {P : Prop} : prop_resize P -> P :=
begin
  hsimp, intro p, hinduction LEM P with lem q nq,
  { exact q },
  { have neq : (LEM_Prop_equiv_Two LEM).to_fun P = Two.zero, by   
      change LEM_Prop_Two LEM P = Two.zero; hsimp; rwr lem,
    rwr neq at p, have p' : false, from p, hinduction p' }
end  

@[hott, reducible]
def prp_rinv {P : Prop} : ∀ p : P, prop_resize_to_prop (prop_to_prop_resize p) = p :=
  assume p, is_prop.elim _ p
 
@[hott]
def prop_to_prop_ulift {P : Prop} : P -> prop_ulift P :=
begin
  intro p, exact ulift.up p
end    

@[hott]
def prop_ulift_to_prop {P : Prop} : prop_ulift P -> P:=
begin
  intro p, exact ulift.down p
end    

@[hott]
def pr_rinv : ∀ (P : trunctype.{u} -1), prop_resize.{u v} (prop_ulift.{u v} P) = P :=
begin
  intro P, hinduction LEM P with lem p np,
  { apply inhabited_Prop_eq, 
    { exact prop_to_prop_resize (prop_to_prop_ulift p) },
    { exact p } },
  { apply uninhabited_Prop_eq, 
    { intro p, apply np, apply prop_ulift_to_prop.{u v}, apply prop_resize_to_prop.{u v}, 
      exact p },
    { exact np } }
end 

@[hott]
def False_ulift_eq : prop_ulift.{u v} False = False :=
begin 
  apply uninhabited_Prop_eq, 
  { intro F, hinduction prop_ulift_to_prop F },
  { intro F, hinduction F } 
end

end hott