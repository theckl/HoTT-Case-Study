import hott.init hott.types.trunc

universes u v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv

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
def set_inj_implies_unique_fib {A B : Set} (f : B -> A) : 
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
def id_is_inv_to_id (A : Set) : is_set_inverse_of (id_map A) (id_map A) :=
  let i := id_map A in
  have r_inv : is_set_right_inverse_of i i, from 
    assume a, calc i (i a) = a : by reflexivity,
  have l_inv : is_set_left_inverse_of i i, from 
    assume a, calc i (i a) = a : by reflexivity,
  is_set_inverse_of.mk r_inv l_inv

/- The inverse is uniquely determined. -/
@[hott]
lemma inv_is_unique {A B : Set} (f : A -> B) (g : B -> A) (g' : B -> A) :
  is_set_inverse_of f g -> is_set_inverse_of f g' -> g = g' :=
assume inv_g inv_g', 
have hom : g ~ g', from assume b,
  calc g b = g (f (g' b)) : 
       by rwr (@is_set_inverse_of.r_inv A B f g' inv_g' b)
       ... = g' b : 
       by rwr (@is_set_inverse_of.l_inv A B f g inv_g (g' b)),
eq_of_homotopy hom /- here, function extensionality is used -/

/- Constructing the inverse of a bijection -/
@[hott, reducible, hsimp] 
def inv_of_bijection {A B : Set} (f : bijection A B) : 
  Σ (g : B -> A), is_set_inverse_of f g :=
let f_inj := is_set_bijective.inj f, f_surj := is_set_bijective.surj f in
have inv_f : forall b : B, fiber f b, from assume b, 
  have fp : is_prop (fiber f b), from 
    set_inj_implies_unique_fib _ (f_inj) _, 
  @untrunc_of_is_trunc _ _ fp (f_surj b), 
let g := λ b : B, fiber.point (inv_f b) in
have r_inv_f : is_set_right_inverse_of f g, from 
  assume b, fiber.point_eq (inv_f b),
have l_inv_f : is_set_left_inverse_of f g, from assume a, 
  have fpa : is_prop (fiber f (f a)), from 
    set_inj_implies_unique_fib _ (f_inj) _, 
  ap fiber.point (@is_prop.elim _ fpa (inv_f (f a)) (fiber.mk a (idpath (f a)))), 
sigma.mk g (is_set_inverse_of.mk r_inv_f l_inv_f) 

/- Functions with inverses are bijective. -/
@[hott, reducible, hsimp]
def has_inverse_to_bijection {A B : Set} (f : A -> B) (g : B -> A) :
  is_set_inverse_of f g -> bijection A B :=
assume inv_f_g,
have f_inj : is_set_injective f, from assume a1 a2 feq,
  calc a1 = g (f a1) : by rwr (@is_set_inverse_of.l_inv _ _ f g inv_f_g a1)
      ... = g (f a2) : by rwr feq
      ... = a2 : by rwr (@is_set_inverse_of.l_inv _ _ f g inv_f_g a2),
have f_surj : is_set_surjective f, from assume b, 
  have af : fiber f b, from 
    fiber.mk (g b) (@is_set_inverse_of.r_inv _ _ f g inv_f_g b),
  tr af,
have is_bij : is_set_bijective f, from is_set_bijective.mk f_inj f_surj,
bijection.mk f is_bij

/- The inverse of a bijection is a bijection. -/
@[hott]
def set_inv_inv {A B : Set} (f : A -> B) (g : B -> A) :
  is_set_inverse_of f g -> is_set_inverse_of g f :=
assume inv_f_g,
is_set_inverse_of.mk (@is_set_inverse_of.l_inv _ _ f g inv_f_g) 
                     (@is_set_inverse_of.r_inv _ _ f g inv_f_g)

@[hott, reducible, hsimp]
def inv_bijection_of {A B : Set} (f : bijection A B) : bijection B A :=
  let g := (inv_of_bijection f).1, inv_f_g := (inv_of_bijection f).2 in
  has_inverse_to_bijection g f (set_inv_inv f g inv_f_g)

@[hott]
lemma inv_bij_is_inv {A B : Set} (f : bijection A B) :
  is_set_inverse_of f (inv_bijection_of f) := 
(inv_of_bijection f).2

/- The identity map is a bijection. -/
@[hott, reducible, hsimp]
def identity (A : Set) : bijection A A := 
  let i := id_map A in
  have id_inv : is_set_inverse_of i i, from id_is_inv_to_id A, 
  has_inverse_to_bijection i i id_inv

@[hott]
lemma identity_to_id_map (A : Set) :
  bijection.map (identity A) = id_map A :=
by hsimp

/- The inverse of the identity map is the identity map itself. -/
@[hott]
lemma inv_bij_of_id_id {A : Set} : 
  inv_bijection_of (identity A) = identity A := 
let inv_bij := bijection.map (inv_bijection_of (identity A)) in  
have map_inv_id_id : inv_bij = id_map A, from
  inv_is_unique (id_map A) inv_bij (id_map A) 
                (inv_of_bijection (identity A)).2 (id_is_inv_to_id A), 
bijection_eq_from_map_eq (inv_bijection_of (identity A)) (identity A) map_inv_id_id

/- Equalities between two sets correspond to bijections between the two sets. 
   To make the construction of the equivalence more transparent we split off some 
   auxiliary definitions and lemmas. 
   The equivalence is constructed as a composition of intermediate equivalences. 
   To show right and left inverses we use the behaviour of the equivalence functions
   on the respective identity elements. -/
local notation `car` A := trunctype.carrier A

/- The equivalence between [Set] equalities and equalities of their carriers is also 
   constructed by [trunctype_eq_equiv] in [type.trunc] but it is not reducible, 
   hence cannot be used for calculations. Instead we construct the equivalence
   from scratch, making the functions reducible. -/
@[hott, hsimp]   
def set_eq_to_car_eq {A B : Set} : (A = B) -> ((car A) = (car B)) :=
  assume e, ap trunctype.carrier e

@[hott]
definition idp_set_to_idp_car {A : Set} : set_eq_to_car_eq (idpath A) = idpath (car A) :=
  by hsimp

@[hott, reducible, hsimp]
def car_eq_to_set_eq : Π {A B : Set}, ((car A) = (car B)) -> (A = B) 
| (trunctype.mk car1 struct1) (trunctype.mk car2 struct2) := 
  assume ec, 
  let est := pathover_of_tr_eq (is_prop.elim (ec ▸ struct1) struct2) in
  apd011 Set.mk ec est  

/- It's complicated to do calculations with [car_eq_to_set_eq].-/
@[hott, hsimp]
def idp_car_to_idp_set : 
  Π {A : Set}, car_eq_to_set_eq (idpath (car A)) = idpath A 
| (trunctype.mk carr struct) :=  
  begin
    hsimp,
    have est_eq : pathover_of_tr_eq idp = idpatho struct, from 
      is_prop.elim (pathover_of_tr_eq _) (idpatho struct),
    rwr est_eq
  end

@[hott]
def linv_set_eq_car_eq {A B : Set} : forall (es : A = B),
  car_eq_to_set_eq (set_eq_to_car_eq es) = es :=
let car_set := λ (A B : Set) (e : A = B), car_eq_to_set_eq (set_eq_to_car_eq e) = e in   
have H : forall (A : Set), car_set A A idp, from 
  assume A,
  calc  car_eq_to_set_eq (set_eq_to_car_eq (idpath A)) = 
              car_eq_to_set_eq (idpath (car A)) : by hsimp
        ... = idpath A : idp_car_to_idp_set,
assume es, rec_unbased H es

/- This should be shown for general structures consisting of a type and
   a dependent proposition. -/
@[hott]   
lemma ap_car_apd011_set_mk {cA cB: Type _} :
  Π (ec :cA = cB) [s : is_set cA] [t : is_set cB] (est : s =[ec] t), 
  ap trunctype.carrier (apd011 Set.mk ec est) = ec := 
have H_ec : Π (cA : Type _) (s t : is_set cA) (est : s =[idpath cA] t), 
         ap trunctype.carrier (apd011 Set.mk (idpath cA) est) = idpath cA, from
  assume cA s t est,
  have H_est : Π (s : is_set cA), 
    ap trunctype.carrier (apd011 Set.mk (idpath cA) (idpatho s)) = idpath cA, from
    assume s, by reflexivity, 
  let P := λ (t : is_set cA) (est : s =[idpath cA] t), 
     ap trunctype.carrier (apd011 Set.mk (idpath cA) est) = idpath cA in   
  @idp_rec_on _ _ _ _ P _ est (H_est s),  
let P := λ (cA cB) (ec : cA = cB), Π (s : is_set cA) (t : is_set cB) 
     (est : s =[ec] t), ap trunctype.carrier (apd011 Set.mk ec est) = ec in 
assume ec, @rec_unbased _ P H_ec _ _ ec

@[hott]
lemma rinv_set_eq_car_eq : Π {A B : Set}, forall (ec : (car A) = (car B)),
  set_eq_to_car_eq (car_eq_to_set_eq ec) = ec
| (trunctype.mk carr1 struct1) (trunctype.mk carr2 struct2) := 
  assume ec, 
  let est := pathover_of_tr_eq (is_prop.elim (ec ▸ struct1) struct2) in  
  calc set_eq_to_car_eq (car_eq_to_set_eq ec) = ap trunctype.carrier (car_eq_to_set_eq ec) : 
       by hsimp 
       ... = ap trunctype.carrier (apd011 Set.mk ec est) : 
       by reflexivity
       ... = ec : by rwr @ap_car_apd011_set_mk _ _ ec struct1 struct2 est

@[hott]
def set_eq_equiv_car_eq {A B : Set} : (A = B) ≃ ((car A) = (car B)) :=
  equiv.mk set_eq_to_car_eq (hott.is_equiv.adjointify set_eq_to_car_eq car_eq_to_set_eq 
                                        rinv_set_eq_car_eq linv_set_eq_car_eq)

@[hott]
def car_eq_equiv_car_eqv {A B : Set} : ((car A) = (car B)) ≃ ((car A) ≃ (car B)) :=
  eq_equiv_equiv _ _    /- Here, univalence is used. -/

@[hott]
def car_eq_to_car_eqv {A B : Set} : ((car A) = (car B)) -> ((car A) ≃ (car B)) :=
  equiv.to_fun car_eq_equiv_car_eqv

@[hott]
def car_eqv_to_car_eq {A B : Set} : ((car A) ≃ (car B)) -> ((car A) = (car B)) :=
  (equiv.to_fun car_eq_equiv_car_eqv)⁻¹ᶠ

@[hott]
def id_map_eqv (A : Set) : (car A) ≃ (car A) :=
  equiv.mk (id_map A) (hott.is_equiv.is_equiv_id (car A))

end set

end hott
