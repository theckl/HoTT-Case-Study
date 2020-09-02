import hott.init hott.types.trunc

universes u v w
hott_theory

namespace hott
open is_trunc 

/- Should be in [init.function]. -/
@[inline, reducible] def function.comp {α β φ : Type _} (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

hott_theory_cmd "local infixr  ` ∘ `:80      := hott.function.comp"


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

@[hott]
lemma id_map_is_right_neutral {A B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=  
by hsimp   

@[hott, class]
def is_set_injective {A B : Set} (f : B -> A) := 
  forall b1 b2 : B, f b1 = f b2 -> b1 = b2

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
let P := assume b1, forall b2 : B, f b1 = f b2 -> b1 = b2 in 
@is_prop_dprod B P eq_b2   

/- fibers of injective maps only contain one element. -/
@[hott]
theorem set_inj_implies_unique_fib {A B : Set} (f : B -> A) : 
  is_set_injective f -> forall a : A, is_prop (fiber f a) :=
assume f_inj a,
have H : forall fb1 fb2 : fiber f a, fb1 = fb2, from
  assume fb1 fb2,
  match fb1, fb2 with fiber.mk b1 e1, fiber.mk b2 e2 :=    
    have eqb : b1 = b2, from f_inj b1 b2 (e1 ⬝ e2⁻¹), 
    have eqbeq : e1 =[eqb;(λ b : B, f b = a)] e2, from pathover_of_tr_eq (is_set.elim _ _),
    apd011 fiber.mk eqb eqbeq 
  end,  
is_prop.mk H 

/- This is the universal property of injective maps. -/
@[hott]
lemma univ_prop_of_inj {A B : Set} (i : A -> B) (i_inj : is_set_injective i) : 
  forall (C : Set) (f g : C -> A), i ∘ f = i ∘ g -> f = g :=
assume C f g comp_eq, 
have i_hom : forall c : C, i (f c) = i (g c), from 
  assume c, 
  calc i (f c) = (i ∘ f) c : by reflexivity
           ... = (i ∘ g) c : by rwr comp_eq
           ... = i (g c) : by reflexivity,             
have hom : f ~ g, from assume c, i_inj (f c) (g c) (i_hom c),         
eq_of_homotopy hom  

@[hott, class]
def is_set_surjective {A B : Set} (f : B -> A) :=
  forall a : A, image f a

@[hott, instance]
lemma is_set_surj_is_prop {A B : Set} (f : B -> A): 
  is_prop (is_set_surjective f) :=
have forall a : A, is_prop (image f a), from assume a, by apply_instance, 
have pre_im_is_prop : is_prop (forall a : A, image f a), from
  is_prop_dprod this,
have surj_eq : forall surj1 surj2 : is_set_surjective f, surj1 = surj2, from
  assume surj1 surj2, 
  @is_prop.elim _ pre_im_is_prop surj1 surj2,  
is_prop.mk surj_eq   

@[hott]
class is_set_bijective {A B : Set} (f : B -> A) := 
 (inj : is_set_injective f) (surj : is_set_surjective f)

@[hott, instance]
lemma is_set_bij_is_prop {A B : Set} (f : B -> A) : 
  is_prop (is_set_bijective f) :=
have H : forall bij1 bij2 : is_set_bijective f, bij1 = bij2, from
  assume bij1 bij2,
  match bij1, bij2 with (is_set_bijective.mk inj1 surj1), (is_set_bijective.mk inj2 surj2) := 
    ap011 is_set_bijective.mk (is_prop.elim inj1 inj2)(is_prop.elim surj1 surj2) 
  end,
is_prop.mk H

/- Bijective maps, bundled up and provided with a coercion. -/
@[hott]
structure bijection (A B : Set) :=
  (map: A -> B) (bij : is_set_bijective map)

@[hott]
instance bij_to_map (A B : Set) : 
  has_coe_to_fun (bijection A B) :=
has_coe_to_fun.mk (λ _, A -> B) (λ f, f.map)

attribute [instance] bijection.bij 

@[hott]
lemma bijection_eq_from_map_eq {A B : Set} : 
  forall f g : bijection A B, bijection.map f = bijection.map g -> f = g  
| (bijection.mk map1 bij1) (bijection.mk map2 bij2) := 
   assume map_eq, 
   have tr_eq : map_eq ▸ bij1 = bij2, from
     is_prop.elim (map_eq ▸ bij1) (bij2), 
   have is_bij_eq : bij1 =[map_eq] bij2, from pathover_of_tr_eq tr_eq,
   apd011 bijection.mk map_eq is_bij_eq

@[hott]
lemma map_eq_from_bijection_eq {A B : Set} :
  forall f g : bijection A B, f = g -> bijection.map f = bijection.map g :=
assume f g map_eq, ap bijection.map map_eq

/- Note that equality of two bijections and equality of the two underlying sets
   are propositions (not proven), so constructing an equivalence is useless. 
   Similarly, the idpaths must be mapped to each other. -/

@[hott]
def is_set_right_inverse_of {A B : Set} (f : A -> B) (g : B -> A) :=
  forall b, f (g b) = b

@[hott]
def is_set_left_inverse_of {A B : Set} (f : A -> B) (g : B -> A) :=
  forall a, g (f a) = a

@[hott]
class is_set_inverse_of {A B : Set} (f : A -> B) (g : B -> A) := 
  (r_inv : is_set_right_inverse_of f g) (l_inv : is_set_left_inverse_of f g)

@[hott]
lemma id_is_inv_to_id (A : Set) : is_set_inverse_of (id_map A) (id_map A) :=
  let i := id_map A in
  have r_inv : is_set_right_inverse_of i i, from 
    assume a, calc i (i a) = a : by reflexivity,
  have l_inv : is_set_left_inverse_of i i, from 
    assume a, calc i (i a) = a : by reflexivity,
  is_set_inverse_of.mk r_inv l_inv

end set

end hott
