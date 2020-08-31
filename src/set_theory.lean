import hott.init hott.types.trunc

universes u v w
hott_theory

namespace hott
open is_trunc 

namespace set

/- We need the empty set, the identity map between sets and some properties of maps between sets. They can be 
   derived from properties of general (n-)types, in [function], but we give them separate definitions adapted 
   to sets, to make them more accessible. -/

@[hott]
def empty_Set : Set := 
  Set.mk empty (is_trunc_succ empty -1)

@[hott, hsimp, reducible]
def id {A : Type u} (a : A) : A := a 

@[hott, hsimp, reducible]
def id_map (A : Set) : A -> A := @id A   

/- The following lemma (not the proof) produces a universe error.
   We replace it by the next lemma until the possible bug is 
   resolved. -/
/- 
@[hott]
lemma id_map_is_right_neutral {A B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=  
by { hsimp, exact rfl }   
-/

@[hott, hsimp, reducible]
lemma id_map_rn {A B : Set} (map : A -> B) :
  forall a : A, (map ∘ (id_map A)) a = map a :=
assume a, refl (map a) 

@[hott]
class is_set_injective {A B : Set} (f : B -> A) := 
  (inj_imp : forall b1 b2 : B, f b1 = f b2 -> b1 = b2)

/- The next 2 lemmas should be (and are?) in one of the trunc-files. -/
@[hott]
lemma is_prop_map {A B : Type _} (pB : is_prop B) : is_prop (A -> B) :=
have eq_map : forall f1 f2 : A -> B, f1 = f2, from 
  assume f1 f2, 
  have map_hom : f1 ~ f2, from 
    assume a, is_prop.elim _ _, 
  eq_of_homotopy map_hom,
is_prop.mk eq_map 

@[hott]
lemma is_prop_dprod {A : Type _} {P : A -> Type _} 
    (pP : forall a : A, is_prop (P a)) : 
  is_prop (forall a : A, P a) :=
have eq_prod : forall dP1 dP2 : (forall a : A, P a), dP1 = dP2, from 
  assume dP1 dP2, 
  have dP_hom : dP1 ~ dP2, from 
    assume a, 
    is_prop.elim _ _, 
  eq_of_homotopy dP_hom,
is_prop.mk eq_prod  

/- Maps between two given sets are sets. 
   Looks like a HoTT-ism, but is actually a rule to construct sets from known sets. -/
@[hott]
lemma is_set_map {A B : Set} : is_set (A -> B) :=
have H : forall (f g : A -> B) (p q : f = g), p = q, from   
  assume f g p q, 
  have eq_eqv_hom : (f = g) ≃ (f ~ g), from 
    eq_equiv_homotopy f g, /- uses function extensionality -/ 
  have is_prop_hom : is_prop (f ~ g), from 
    have pP : forall a : A, is_prop (f a = g a), from 
      assume a, is_trunc_eq -1 (f a) (g a),
    @is_prop_dprod _ (λ a : A, f a = g a) pP, 
  have H_eqv : is_prop (f = g), from 
    is_trunc_is_equiv_closed -1 (equiv.to_fun eq_eqv_hom)⁻¹ᶠ is_prop_hom, 
  @is_prop.elim _ H_eqv p q, 
is_set.mk (A -> B) H

/- That is a HoTT-ism, but should be automatable. -/
@[hott, instance]
lemma is_set_inj_is_prop {A B : Set} (f : B -> A): 
  is_prop (is_set_injective f) := 
have eq_imp : forall b1 b2 : B, is_prop (f b1 = f b2 -> b1 = b2), from 
  assume b1 b2, is_prop_map (is_trunc_eq -1 b1 b2),
have eq_b2 : forall b1 : B, is_prop (forall b2 : B, f b1 = f b2 -> b1 = b2), from
  assume b1, is_prop_dprod (eq_imp b1),
have is_prop_inj_imp : is_prop (forall b1 b2 : B, f b1 = f b2 -> b1 = b2), from 
  let P := assume b1, forall b2 : B, f b1 = f b2 -> b1 = b2 in 
  @is_prop_dprod B P eq_b2,   
have eq_is_inj : forall inj1 inj2 : is_set_injective f, inj1 = inj2, from
  assume inj1 inj2,
  match inj1, inj2 with is_set_injective.mk inj_imp1, is_set_injective.mk inj_imp2 :=
    ap is_set_injective.mk (@is_prop.elim _ is_prop_inj_imp inj_imp1 inj_imp2)
  end,  
is_prop.mk eq_is_inj

/- fibers of injective maps only contain one element. -/
@[hott]
theorem set_inj_implies_unique_fib {A B : Set} (f : B -> A) : 
  is_set_injective f -> forall a : A, is_prop (fiber f a) :=
assume f_inj a,
let inj_imp_f := f_inj.inj_imp in
have H : forall fb1 fb2 : fiber f a, fb1 = fb2, from
  assume fb1 fb2,
  match fb1, fb2 with fiber.mk b1 e1, fiber.mk b2 e2 :=    
    have eqb : b1 = b2, from inj_imp_f b1 b2 (e1 ⬝ e2⁻¹), 
    have eqbeq : e1 =[eqb;(λ b : B, f b = a)] e2, from pathover_of_tr_eq (is_set.elim _ _),
    apd011 fiber.mk eqb eqbeq 
  end,  
is_prop.mk H 

end set

end hott
