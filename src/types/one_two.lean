import str_id 

universes u v w
hott_theory

namespace hott
open hott.is_trunc 

/- We need a set-type `Two` with two objects to deduce propositional resizing from LEM.
   To construct it we also need `Zero` and `One`. 

   [Zero] and [One] are equivalent to [true] and [false] in [prop_logic], but
   we want to use them without logical connotations. -/
@[hott]  --[GEVE]
inductive Zero : Type _

@[hott]
def eq_Zero : forall f₁ f₂ : Zero, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance] --[GEVE]
def Zero_is_prop : is_prop Zero :=
  is_prop.mk eq_Zero 

@[hott]
def Zero_Set : Set :=
  Set.mk Zero (is_trunc_succ Zero -1)

@[hott, instance]
def is_prop_Zero_equiv (A : Type _) : is_prop (Zero ≃ A) :=
begin 
  apply is_prop.mk, intros eqv₁ eqv₂,
  have H : is_prop A, from is_trunc_equiv_closed -1 eqv₁ Zero_is_prop, 
  hinduction eqv₁ with f₁ is_eqv₁, hinduction eqv₂ with f₂ is_eqv₂,
  fapply apd011 equiv.mk, 
  { apply eq_of_homotopy, intro o, exact @is_prop.elim _ H _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]  --[GEVE]
inductive One : Type _  
| star : One

@[hott] --[GEVE]
def eq_One : forall t₁ t₂ : One, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl One.star),
end 

@[hott, instance]
def One_dec_eq : decidable_eq One := assume t₁ t₂, decidable.inl (eq_One t₁ t₂) 

@[hott, instance] --[GEVE]
def One_is_prop : is_prop One :=
  is_prop.mk eq_One

@[hott]
def One_Set : Set :=
  Set.mk One (is_trunc_succ One -1)

@[hott, instance]
def is_prop_One_equiv (A : Type _) : is_prop (One ≃ A) :=
begin 
  apply is_prop.mk, intros eqv₁ eqv₂,
  have H : is_prop A, from is_trunc_equiv_closed -1 eqv₁ One_is_prop, 
  hinduction eqv₁ with f₁ is_eqv₁, hinduction eqv₂ with f₂ is_eqv₂,
  fapply apd011 equiv.mk, 
  { apply eq_of_homotopy, intro o, exact @is_prop.elim _ H _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]
inductive Two : Type _  --[GEVE]
| zero : Two 
| one : Two 

/- We prove that [Two] is a set using the Fundamental Identity Theorem, 
   following [Rijke-Book, 11.3]. This is a streamlined version of the
   encode-decode method presented in [HoTT-book, Sec.2.13], getting rid 
   of the decoding. -/
@[hott, hsimp]
def code_Two : Two -> Two -> Type _ :=
begin
  intros t₁ t₂, 
  hinduction t₁,
    hinduction t₂, exact One, exact Zero,
    hinduction t₂, exact Zero, exact One,
end  

@[hott, instance]
def code_Two_is_prop : Π t₁ t₂ : Two, is_prop (code_Two t₁ t₂) :=
begin
  intros t₁ t₂, hinduction t₁, 
  hinduction t₂, exact One_is_prop, exact Zero_is_prop,
  hinduction t₂, exact Zero_is_prop, exact One_is_prop,
end

@[hott]
def refl_Two : Π t : Two, code_Two t t := 
begin intro t; hinduction t; exact One.star; exact One.star end

@[hott, hsimp]
def encode_Two : Π t₁ t₂ : Two, (t₁ = t₂) -> code_Two t₁ t₂ :=
  assume t₁ t₂ eq, eq ▸[λ t : Two, code_Two t₁ t] (refl_Two t₁)

@[hott] --[GEVE]
def Two_eq_equiv_code : ∀ t₁ t₂ : Two, (t₁ = t₂) ≃ code_Two t₁ t₂ := 
begin 
  intros t₁ t₂, 
  let R := ppred.mk (λ t₂ : Two, code_Two t₁ t₂) (refl_Two t₁),
  let f := @ppmap.mk _ _ (id_ppred t₁) R 
                    (λ t₂ : Two, encode_Two t₁ t₂) idp, 
  fapply equiv.mk, exact encode_Two t₁ t₂,
  apply tot_space_contr_ppmap_id_eqv R f, fapply is_contr.mk,
  exact ⟨t₁, refl_Two t₁⟩, intro tp, hinduction tp with t ct, 
  hinduction t₁, 
    hinduction t, hinduction ct; refl, exact Zero.rec _ ct,  
    hinduction t, exact Zero.rec _ ct, hinduction ct; refl
  end  

@[hott, instance] --[GEVE]
def Two_eq_is_prop : Π (t₁ t₂ : Two.{u}), is_prop (t₁ = t₂) :=
  λ t₁ t₂ : Two, is_trunc_equiv_closed_rev.{u u} 
          -1 (Two_eq_equiv_code t₁ t₂) (code_Two_is_prop t₁ t₂)

@[hott, instance]
def Two_is_set : is_set Two :=
  is_trunc_succ_intro (λ t₁ t₂, Two_eq_is_prop t₁ t₂)

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

end hott