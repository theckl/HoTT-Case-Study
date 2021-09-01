import hott.init init2 hott.types.trunc prop_logic hott.types.prod hott.hit.quotient 
       hott.algebra.relation types2

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv hott.prod hott.quotient hott.sigma hott.relation

namespace set

set_option pp.universes true

/- `Prop`s are `Set`s. -/
@[hott]
def Prop_to_Set : Prop -> Set :=
  λ P, Set.mk P (is_trunc_succ P -1)

/- Nicer name for construction of `Set` from `is_set`. -/
@[hott]
def to_Set (A : Type _) [pA : is_set A] : Set :=
  trunctype.mk A pA    

/- We need the empty set, the identity map between sets and some properties of maps between sets. They can be 
   derived from properties of general (n-)types, in [function], but we give them separate definitions adapted 
   to sets, to make them more accessible. -/

/- The empty set is polyversic as [false] is polyversic. If we defined it instead
   with [empty] it would be of [Type 0] because [empty] is of [Type 0] -/
@[hott]
def empty_Set : Set := 
  Set.mk false (is_trunc_succ false -1)

@[hott, hsimp, reducible]
def id_map (A : Set) : A -> A := @id A  

@[hott]
def id_map_is_right_neutral {A : Set} {B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=  
by hsimp   

@[hott, class]
def is_set_injective {A : Set} {B : Set} (f : B -> A) := 
  forall b1 b2 : B, f b1 = f b2 -> b1 = b2

@[hott, instance]
def comp_inj_inj {A B C : Set} (f : A -> B) (g : B -> C) [f_inj : is_set_injective f] 
  [g_inj : is_set_injective g] : is_set_injective (g ∘ f) :=
assume a₁ a₂ gf_eq,
have f_eq : f a₁ = f a₂, from g_inj (f a₁) (f a₂) gf_eq,
f_inj a₁ a₂ f_eq

/- Maps between two given sets are sets. 
   Looks like a HoTT-ism, but is actually a rule to construct sets from known sets. -/
@[hott, instance]
def is_set_map {A : Set} {B : Set} : is_set (A -> B) :=
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

/- The dependent version; the bundled set will yield the categorical product of sets. -/
@[hott, instance]
def is_set_dmap {A : Set} {B : A -> Set} : is_set (Π (a : A), B a) :=
  have H : forall (f g : Π (a : A), B a) (p q : f = g), p = q, from 
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
  is_set.mk (Π (a : A), B a) H

@[hott]
def Sections {A : Set} (B : A -> Set) : Set :=
  Set.mk (Π (a : A), B a) (@is_set_dmap _ _)  

/- That is a HoTT-ism, but should be automatable. -/
@[hott, instance]
lemma is_set_inj_is_prop {A : Set} {B : Set} (f : B -> A): 
  is_prop (is_set_injective f) := 
have eq_imp : forall b1 b2 : B, is_prop (f b1 = f b2 -> b1 = b2), from 
  assume b1 b2, is_prop_map (is_trunc_eq -1 b1 b2),
have eq_b2 : forall b1 : B, is_prop (forall b2 : B, f b1 = f b2 -> b1 = b2), from
  assume b1, is_prop_dprod (eq_imp b1),
let P := assume b1, forall b2 : B, f b1 = f b2 -> b1 = b2 in 
@is_prop_dprod B P eq_b2   

/- fibers of injective maps only contain one element. -/
@[hott]
def set_inj_implies_unique_fib {A : Set} {B : Set} (f : B -> A) : 
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
lemma univ_prop_of_inj {A : Set} {B : Set} (i : A -> B) (i_inj : is_set_injective i) : 
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
def is_set_surjective {A : Set} {B : Set} (f : B -> A) :=
  forall a : A, image f a

@[hott, instance]
lemma is_set_surj_is_prop {A : Set} {B : Set} (f : B -> A): 
  is_prop (is_set_surjective f) :=
have forall a : A, is_prop (image f a), from assume a, by apply_instance, 
have pre_im_is_prop : is_prop (forall a : A, image f a), from
  is_prop_dprod this,
have surj_eq : forall surj1 surj2 : is_set_surjective f, surj1 = surj2, from
  assume surj1 surj2, 
  @is_prop.elim _ pre_im_is_prop surj1 surj2,  
is_prop.mk surj_eq   

@[hott]
class is_set_bijective {A : Set} {B : Set} (f : B -> A) := 
 (inj : is_set_injective f) (surj : is_set_surjective f)

@[hott, instance]
lemma is_set_bij_is_prop {A : Set} {B : Set} (f : B -> A) : 
  is_prop (is_set_bijective f) :=
have H : forall bij1 bij2 : is_set_bijective f, bij1 = bij2, from
  assume bij1 bij2,
  match bij1, bij2 with (is_set_bijective.mk inj1 surj1), (is_set_bijective.mk inj2 surj2) := 
    ap011 is_set_bijective.mk (is_prop.elim inj1 inj2)(is_prop.elim surj1 surj2) 
  end,
is_prop.mk H

/- Bijective maps, bundled up and provided with a coercion and providing an instance. -/
@[hott]
structure bijection (A : Set) (B : Set) :=
  (map: A -> B) (bij : is_set_bijective map)

@[hott]
instance bij_to_map (A : Set) (B : Set) : 
  has_coe_to_fun (bijection A B) :=
has_coe_to_fun.mk (λ _, A -> B) (λ f, f.map)

attribute [instance] bijection.bij 

@[hott]
lemma bijection_eq_from_map_eq {A : Set} {B : Set}: 
  forall f g : bijection A B, bijection.map f = bijection.map g -> f = g  
| (bijection.mk map1 bij1) (bijection.mk map2 bij2) := 
   assume map_eq, 
   have tr_eq : map_eq ▸ bij1 = bij2, from
     is_prop.elim (map_eq ▸ bij1) (bij2), 
   have is_bij_eq : bij1 =[map_eq] bij2, from pathover_of_tr_eq tr_eq,
   apd011 bijection.mk map_eq is_bij_eq

@[hott]
lemma map_eq_from_bijection_eq {A : Set} {B : Set}:
  forall f g : bijection A B, f = g -> bijection.map f = bijection.map g :=
assume f g map_eq, ap bijection.map map_eq

/- Note that equality of two bijections and equality of the two underlying sets
   are propositions (not proven), so constructing an equivalence is useless. 
   Similarly, the idpaths must be mapped to each other. -/

@[hott]
def is_set_right_inverse_of {A : Set} {B : Set} (f : A -> B) (g : B -> A) :=
  forall b, f (g b) = b

@[hott, reducible]
def is_set_left_inverse_of {A : Set} {B : Set} (f : A -> B) (g : B -> A) :=
  forall a, g (f a) = a

@[hott]
class is_set_inverse_of {A : Set} {B : Set} (f : A -> B) (g : B -> A) := 
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
lemma inv_is_unique {A : Set} {B : Set} (f : A -> B) (g : B -> A) (g' : B -> A) :
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
def inv_of_bijection {A : Set} {B : Set} (f : bijection A B) : 
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
def has_inverse_to_bijection {A : Set} {B : Set} (f : A -> B) (g : B -> A) :
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
def set_inv_inv {A : Set} {B : Set} (f : A -> B) (g : B -> A) :
  is_set_inverse_of f g -> is_set_inverse_of g f :=
assume inv_f_g,
is_set_inverse_of.mk (@is_set_inverse_of.l_inv _ _ f g inv_f_g) 
                     (@is_set_inverse_of.r_inv _ _ f g inv_f_g)

@[hott, reducible, hsimp]
def inv_bijection_of {A : Set} {B : Set} (f : bijection A B) : bijection B A :=
  let g := (inv_of_bijection f).1, inv_f_g := (inv_of_bijection f).2 in
  has_inverse_to_bijection g f (set_inv_inv f g inv_f_g)

@[hott]
lemma inv_bij_is_inv {A : Set} {B : Set} (f : bijection A B) :
  is_set_inverse_of f (inv_bijection_of f) := 
(inv_of_bijection f).2

/- The identity map is a bijection. -/
@[hott, reducible, hsimp]
def identity (A : Set) : bijection A A := 
  let i := id_map A in
  have id_inv : is_set_inverse_of i i, from id_is_inv_to_id A, 
  has_inverse_to_bijection i i id_inv

@[hott]
def identity_to_id_map (A : Set) :
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
@[hott, hsimp, reducible]   
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
    have est_eq : (pathover_idp_of_eq (is_trunc 0) idp) = idpatho struct, from 
      is_prop.elim (pathover_of_tr_eq _) (idpatho struct),
    rwr est_eq
  end

@[hott]
def linv_set_eq_car_eq {A B : Set} : forall (es : A = B),
  car_eq_to_set_eq (set_eq_to_car_eq es) = es :=
begin 
  intro es,
  hinduction es,
  hsimp 
end   

/- This should be shown for general structures consisting of a type and
   a dependent proposition. -/
@[hott]   
lemma ap_car_apd011_set_mk {cA cB: Type _} :
  Π (ec : cA = cB) [s : is_set cA] [t : is_set cB] (est : s =[ec] t), 
  ap trunctype.carrier (apd011 Set.mk ec est) = ec := 
begin 
  intro ec,
  hinduction ec,
    intros s t est,
    hinduction est,
    reflexivity
end   

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

@[hott, hsimp]
def car_eq_equiv_car_eqv {A B : Set} : ((car A) = (car B)) ≃ ((car A) ≃ (car B)) :=
  eq_equiv_equiv _ _    /- Here, univalence is used. -/

@[hott, hsimp]
def car_eq_to_car_eqv {A B : Set} : ((car A) = (car B)) -> ((car A) ≃ (car B)) :=
  equiv.to_fun car_eq_equiv_car_eqv

@[hott, hsimp]
def car_eqv_to_car_eq {A B : Set} : ((car A) ≃ (car B)) -> ((car A) = (car B)) :=
  (equiv.to_fun car_eq_equiv_car_eqv)⁻¹ᶠ

@[hott, hsimp]
def id_map_eqv (A : Set) : (car A) ≃ (car A) :=
  equiv.mk (id_map A) (hott.is_equiv.is_equiv_id (car A))

@[hott, hsimp]
lemma id_to_id_map_eqv (A : Set) : car_eq_to_car_eqv (idpath (car A)) = id_map_eqv A := 
  by reflexivity

@[hott]
lemma id_map_eqv_to_id (A : Set) : car_eqv_to_car_eq (id_map_eqv A) = idpath (car A) := 
  calc car_eqv_to_car_eq (id_map_eqv A) = car_eqv_to_car_eq (car_eq_to_car_eqv (idpath (car A))) :
       ap car_eqv_to_car_eq (id_to_id_map_eqv A)
       ... = idpath (car A) : 
       by exact is_equiv.left_inv car_eq_to_car_eqv (idpath (car A)) 

@[hott, reducible]
def car_eqv_to_bij {A B : Set} : ((car A) ≃ (car B)) -> (bijection A B) :=
  assume f_eqv : (car A) ≃ (car B), 
  let f := equiv.to_fun f_eqv, g := (equiv.to_fun f_eqv)⁻¹ᶠ in
  let inv_f_g := is_set_inverse_of.mk (is_equiv.right_inv f_eqv) (is_equiv.left_inv f_eqv) in
  has_inverse_to_bijection f g inv_f_g 

@[hott, reducible]
def bij_to_car_eqv {A B : Set} : (bijection A B) -> ((car A) ≃ (car B)) :=
assume f : bijection A B, let f_inv := inv_of_bijection f, g := f_inv.1 in
have c : is_set_inverse_of f g, from f_inv.2,
let f_rinv := @is_set_inverse_of.r_inv _ _ f g c, 
    f_linv := @is_set_inverse_of.l_inv _ _ f g c in
equiv.mk f (is_equiv.adjointify f g f_rinv f_linv)

@[hott]
lemma rinv_set_equiv_bijection {A B : Set} : forall f : bijection A B,
  bijection.map (car_eqv_to_bij (bij_to_car_eqv f)) = f :=
let F := @car_eqv_to_bij A B, G := @bij_to_car_eqv A B in
assume f, 
have eq_G : equiv.to_fun (G f) = f, by hsimp,
have eq_F : bijection.map (F (G f)) = equiv.to_fun (G f), by hsimp,
eq_F ⬝ eq_G

@[hott]
lemma linv_bijection_set_equiv {A B : Set} : forall e : (car A) ≃ (car B),
  equiv.to_fun (bij_to_car_eqv (car_eqv_to_bij e)) = e :=
let F := @car_eqv_to_bij A B, G := @bij_to_car_eqv A B in
assume e, 
have eq_F : bijection.map (F e) = equiv.to_fun e, by hsimp,
have eq_G : equiv.to_fun (G (F e)) = bijection.map (F e), by hsimp,
eq_G ▸ eq_F

/- The next 2 lemmas should be in [init.equiv]. -/
@[hott]
def equiv_eq_from_fun_eq {A B : Type u} : forall e1 e2 : A ≃ B, 
  equiv.to_fun e1 = equiv.to_fun e2 -> e1 = e2
| (equiv.mk fun1 is_eqv1) (equiv.mk fun2 is_eqv2) := 
  assume fun_eq, 
  have tr_eq : fun_eq ▸ is_eqv1 = is_eqv2, from
     is_prop.elim (fun_eq ▸ is_eqv1) (is_eqv2),
  have is_equiv_eq : is_eqv1 =[fun_eq] is_eqv2, from pathover_of_tr_eq tr_eq,  
  apd011 equiv.mk fun_eq is_equiv_eq

@[hott]
def fun_eqv_trans_comp_eqv {A B C : Type u} : Π (F : A ≃ B) (G : B ≃ C), 
  equiv.to_fun (equiv.trans F G) = (equiv.to_fun G) ∘ (equiv.to_fun F) :=
assume F G, by reflexivity 

@[hott]
def car_eqv_equiv_bij {A B : Set.{u}} : ((car A) ≃ (car B)) ≃ (bijection A B) :=
  let F := @car_eqv_to_bij A B, G := @bij_to_car_eqv A B in
  have rinv : forall f, F (G f) = f, from assume f, 
    have map_eq : bijection.map (F (G f)) = bijection.map f, from rinv_set_equiv_bijection f,
    bijection_eq_from_map_eq _ _ map_eq, 
  have linv : forall e, G (F e) = e, from assume e,
    have fun_eq : equiv.to_fun (G (F e)) = equiv.to_fun e, from linv_bijection_set_equiv e,
    equiv_eq_from_fun_eq _ _ fun_eq, 
  equiv.mk F (is_equiv.adjointify F G rinv linv)

@[hott]
lemma identity_to_id_eqv (A : Set) : bij_to_car_eqv (identity A) = id_map_eqv A := 
  have fun_eq : equiv.to_fun (bij_to_car_eqv (identity A)) = 
                equiv.to_fun (id_map_eqv A), by reflexivity,
  equiv_eq_from_fun_eq (bij_to_car_eqv (identity A)) (id_map_eqv A) fun_eq

@[hott]
lemma id_eqv_to_identity (A : Set) : car_eqv_to_bij (id_map_eqv A) = identity A := 
  have map_eq : bijection.map (car_eqv_to_bij (id_map_eqv A)) = 
                bijection.map (identity A), by reflexivity, 
  bijection_eq_from_map_eq _ _ map_eq

@[hott]
def set_eq_equiv_bij {A B : Set.{u}} : (A = B) ≃ (bijection A B) :=
  (set_eq_equiv_car_eq ⬝e car_eq_equiv_car_eqv) ⬝e car_eqv_equiv_bij

@[hott]
def set_eq_to_bij {A B : Set.{u}} : A = B -> (bijection A B) :=
  equiv.to_fun set_eq_equiv_bij

@[hott]
def bij_to_set_eq {A B : Set.{u}} : (bijection A B) -> A = B :=
  (equiv.to_fun set_eq_equiv_bij)⁻¹ᶠ

@[hott]
/- These equivalence functions extracted from the equivalences can indeed be used for 
   calculations. -/
lemma identity_to_idp {A : Set} : bij_to_set_eq (identity A) = idpath A :=
calc bij_to_set_eq (identity A) = 
            car_eq_to_set_eq (car_eqv_to_car_eq (bij_to_car_eqv (identity A))) : 
     by reflexivity
     ... =  idpath A : begin rwr identity_to_id_eqv, 
                             rwr id_map_eqv_to_id, 
                             rwr idp_car_to_idp_set end     

@[hott]
def right_inv_set_eq_bij {A B : Set} (f : bijection A B) :
  set_eq_to_bij (bij_to_set_eq f) = f :=
@is_equiv.right_inv (A = B) (bijection A B) set_eq_to_bij _ f

@[hott]
lemma hom_eq_tr_eq {A B : Set} (e : A = B) :
  forall a : A, set_eq_to_bij e a = e ▸ a :=
begin 
  intro a,
  hinduction e,
  reflexivity
end   

@[hott]
lemma bij_hom_tr_eq {A B : Set} (f : bijection A B) : 
  forall a : A, f a = (bij_to_set_eq f) ▸ a := 
let rinv := right_inv_set_eq_bij f, 
    eq_f := bij_to_set_eq f in
assume a,  
calc f a = set_eq_to_bij eq_f a : apd10 (ap bijection.map (eq.inverse rinv)) a
     ... = eq_f ▸ a : hom_eq_tr_eq eq_f a 

end set

namespace set

/- The Cartesian product of two sets is a set. -/
@[hott]
def prod_of_Sets_is_set (A : Set) (B : Set) : is_set (A × B) :=
  have pr_eq : ∀ (p₁ p₂ : A × B) (q r : p₁ = p₂), q = r, from
    assume p₁ p₂ q r, 
    begin
      rwr <- prod_eq_eta q, rwr <- prod_eq_eta r, 
      apply prod_eq_eq,
      apply is_set.elim, apply is_set.elim
    end,  
  is_set.mk _ pr_eq 

@[hott]
def Prod_Set (A : Set) (B : Set) : Set :=
  Set.mk (A × B) (prod_of_Sets_is_set A B)  

notation A ` × `:100 B := Prod_Set A B   

/- Pathover equalities of set elements are equal. -/
@[hott]
def set_po_eq {A : Set} {B : A -> Set} {a₁ a₂ : A} {p : a₁ = a₂} {b₁ : B a₁} {b₂ : B a₂}
  (q r : b₁ =[p; λ a, B a] b₂) : q = r := 
begin 
  rwr <- is_equiv.left_inv (pathover_equiv_tr_eq p b₁ b₂) q,
  rwr <- is_equiv.left_inv (pathover_equiv_tr_eq p b₁ b₂) r,
  apply ap (⇑(pathover_equiv_tr_eq p b₁ b₂))⁻¹ᶠ,
  exact is_set.elim _ _
end   

/- The dependent product of sets is a set. -/
@[hott, instance]
def dprod_of_Sets_is_set (A : Set) (B : A -> Set) : is_set (Σ (a : A), B a) :=
  have dpr_eq : ∀ (p₁ p₂ : Σ (a : A), B a) (q r : p₁ = p₂), q = r, from
    assume p₁ p₂ q r, 
    begin 
      hinduction p₁ with a₁ b₁, hinduction p₂ with a₂ b₂, 
      rwr <- sigma_eq_eta q, rwr <- sigma_eq_eta r,
      have s₁ : q..1 = r..1, from is_set.elim _ _,
      have s₂ : q..2 =[s₁; λ s : a₁ = a₂, b₁ =[s; λ a, B a] b₂] r..2, from 
        begin apply pathover_of_tr_eq, exact set_po_eq _ _ end,
      exact apd011 sigma_eq s₁ s₂
    end,
  is_set.mk _ dpr_eq

@[hott]
def dprod_Set (A : Set) (B : A -> Set) : Set :=
  Set.mk (Σ (a : A), B a) (dprod_of_Sets_is_set A B)   

/- The sum of sets is a set. This is contianed in the file [types.sum] of the HoTT3 library
   which does ot compile. -/
@[hott, instance]
def sum_of_Sets_is_set (A B : Set) : is_set (A ⊎ B) :=
begin
  apply is_trunc_succ_intro, intros z z',
  apply is_trunc_equiv_closed_rev, apply sum_eq_equiv,
  hinduction z with a b; hinduction z' with a' b'; hsimp; apply_instance
end  

@[hott]
def sum_Set (A B : Set) : Set :=
  Set.mk (A ⊎ B) (sum_of_Sets_is_set A B)    

/- We construct finite sets of arbitrary using the sum of sets in induction. -/
@[hott]
def fin_Set (n : ℕ) : Set.{0} :=
begin hinduction n with n fin_n, exact Zero_Set, exact sum_Set fin_n One_Set end  

end set

end hott