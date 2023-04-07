import hott.init init2 hott.types.trunc prop_logic hott.types.prod hott.hit.quotient 
       hott.algebra.relation types2 hott.types.nat.order

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv hott.prod hott.quotient hott.sigma hott.relation 
     nat 

namespace set

set_option pp.universes false

/- `Prop`s are `Set`s. -/
@[hott]
def Prop_to_Set : Prop -> Set :=
  λ P, Set.mk P (is_trunc_succ P -1)

/- Nicer name for construction of `Set` from `is_set`. -/
@[hott]
def to_Set (A : Type _) [pA : is_set A] : Set :=
  trunctype.mk A pA  

/- To deal with equalities of sets it is better to define sets as
   Σ-types, not as structures. -/
@[hott]
def Set_str_equiv_sig : Set ≃ Σ (A : Type _), is_set A :=
begin
  fapply equiv.mk, 
  { intro A, exact dpair A.carrier A.struct },
  { fapply is_equiv.adjointify, 
    { intro sig_set, exact trunctype.mk sig_set.1 sig_set.2 }, 
    { intro sig_set, hinduction sig_set, fapply sigma.sigma_eq, 
      refl, refl },
    { intro A, hinduction A, fapply apd011 trunctype.mk, 
      refl, refl } }
end    

/- We need the empty set, the identity map between sets and some properties of maps between sets. They can be 
   derived from properties of general (n-)types, in [function], but we give them separate definitions adapted 
   to sets, to make them more accessible. -/

/- The empty set is polyversic as [false] is polyversic. If we defined it instead
   with [empty] it would be of [Type 0] because [empty] is of [Type 0] -/
@[hott]
def empty_Set : Set := 
  Set.mk false (is_trunc_succ false -1)

@[hott]
def empty_map (C : Type _) : empty_Set -> C :=
begin intro f, hinduction f end    

@[hott, hsimp, reducible]
def id_map (A : Set) : A -> A := @id A  

@[hott]
def id_map_is_right_neutral {A : Set} {B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=  
by hsimp   

@[hott, class]
def is_set_injective {A : Set} {B : Set} (f : B -> A) := 
  forall b1 b2 : B, f b1 = f b2 -> b1 = b2

/- Set injectivity implies injectivity of maps between types, shown in [types2]. -/
@[hott]
def set_inj_to_type_inj {A : Set} {B : Set} (f : B -> A) :
  (is_set_injective f) -> is_injective f :=
begin 
  intro inj, intros b1 b2, fapply is_equiv.adjointify, 
  { exact inj b1 b2 },
  { intro p, exact is_set.elim _ _ },
  { intro q, exact is_set.elim _ _ }
end      

@[hott, instance]
def comp_inj_inj {A B C : Set} (f : A -> B) (g : B -> C) [f_inj : is_set_injective f] 
  [g_inj : is_set_injective g] : is_set_injective (g ∘ f) :=
assume a₁ a₂ gf_eq,
have f_eq : f a₁ = f a₂, from g_inj (f a₁) (f a₂) gf_eq,
f_inj a₁ a₂ f_eq

/- Maps between two given sets are sets. 
   Looks like a HoTT-ism, but is actually a rule to construct sets from known sets. 
   The construction even works if the source of the map is just a type. -/
@[hott, instance]
def is_set_map {A : Type _} {B : Set} : is_set (A -> B) :=
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
def is_set_dmap {A : Type _} {B : A -> Set} : is_set (Π (a : A), B a) :=
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

@[hott, instance]
def is_set_dmap' {A : Type _} {B : A -> Type _} [H : Π a : A, is_set (B a)] : 
  is_set (Π (a : A), B a) :=
@is_set_dmap A (λ a : A, trunctype.mk (B a) (H a))  

@[hott]
def Sections {A : Set} (B : A -> Set) : Set :=
  Set.mk (Π (a : A), B a) (@is_set_dmap _ _)  

/- That is a HoTT-ism, but should be automatable. -/
@[hott, instance]
def is_set_inj_is_prop {A : Set} {B : Set} (f : B -> A): 
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
def univ_prop_of_inj {A : Set} {B : Set} (i : A -> B) (i_inj : is_set_injective i) : 
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
def is_set_surj_is_prop {A : Set} {B : Set} (f : B -> A): 
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
def is_set_bij_is_prop {A : Set} {B : Set} (f : B -> A) : 
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
def bijection_eq_from_map_eq {A : Set} {B : Set}: 
  forall f g : bijection A B, bijection.map f = bijection.map g -> f = g  
| (bijection.mk map1 bij1) (bijection.mk map2 bij2) := 
   assume map_eq, 
   have tr_eq : map_eq ▸ bij1 = bij2, from
     is_prop.elim (map_eq ▸ bij1) (bij2), 
   have is_bij_eq : bij1 =[map_eq] bij2, from pathover_of_tr_eq tr_eq,
   apd011 bijection.mk map_eq is_bij_eq

@[hott]
def map_eq_from_bijection_eq {A : Set} {B : Set}:
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
def inv_is_unique {A : Set} {B : Set} (f : A -> B) (g : B -> A) (g' : B -> A) :
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

/- The inverse of a bijection is a bijection, and the inverse of the inverse is 
   the bijection itself. -/
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
def mere_inv_bijection {A : Set} {B : Set} (f : ∥bijection A B∥) : ∥bijection B A∥ :=
begin hinduction f with f, exact tr (inv_bijection_of f) end  

@[hott, instance]
def inv_bij_is_inv {A : Set} {B : Set} (f : bijection A B) :
  is_set_inverse_of f (inv_bijection_of f) := 
(inv_of_bijection f).2

@[hott]
def inv_bij_r_inv {A : Set} {B : Set} (f : bijection A B) :
  Π b : B, f ((inv_bijection_of f) b) = b :=
assume b, @is_set_inverse_of.r_inv _ _ _ _ (inv_bij_is_inv f) b  

@[hott]
def inv_bij_l_inv {A : Set} {B : Set} (f : bijection A B) :
  Π a : A, (inv_bijection_of f) (f a) = a :=
assume a, @is_set_inverse_of.l_inv _ _ _ _ (inv_bij_is_inv f) a  

@[hott]
def bij_is_inv_of_bij_inv {A : Set} {B : Set} (f : bijection A B) :
  f = inv_bijection_of (inv_bijection_of f) :=
begin 
  apply bijection_eq_from_map_eq, 
  change f.map = (inv_of_bijection (inv_bijection_of f)).1, 
  apply inv_is_unique (inv_bijection_of f).map,
  { apply set_inv_inv _ _, exact (inv_of_bijection f).2 },
  { exact (inv_of_bijection (inv_bijection_of f)).2 } 
end 

/- The composition of two bijections is a bijection -/
def comp_bijection {A B C : Set} (f : bijection A B) (g : bijection B C) : bijection A C :=
begin
  fapply has_inverse_to_bijection, 
  { exact g ∘ f },
  { exact (inv_bijection_of f) ∘ (inv_bijection_of g) },
  { fapply is_set_inverse_of.mk,
    { intro c, 
      calc g (f ((inv_bijection_of f) ((inv_bijection_of g) c))) = 
                 g ((inv_bijection_of g) c) : 
                 by rwr @is_set_inverse_of.r_inv _ _ f (inv_bijection_of f) _
           ... = c : by rwr @is_set_inverse_of.r_inv _ _ g (inv_bijection_of g) _ },
    { intro a, 
      calc (inv_bijection_of f) ((inv_bijection_of g) (g (f a))) = 
                 (inv_bijection_of f) (f a) : 
                 by rwr @is_set_inverse_of.l_inv _ _ g (inv_bijection_of g) _
           ... = a : by rwr @is_set_inverse_of.l_inv _ _ f (inv_bijection_of f) _ } }
end 

@[hott]
def mere_comp_bijection {A B C : Set} (f : ∥bijection A B∥) (g : ∥bijection B C∥) : ∥bijection A C∥ :=
begin hinduction f with f, hinduction g with g, exact tr (comp_bijection f g) end

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
def inv_bij_of_id_id {A : Set} : 
  inv_bijection_of (identity A) = identity A := 
let inv_bij := bijection.map (inv_bijection_of (identity A)) in  
have map_inv_id_id : inv_bij = id_map A, from
  inv_is_unique (id_map A) inv_bij (id_map A) 
                (inv_of_bijection (identity A)).2 (id_is_inv_to_id A), 
bijection_eq_from_map_eq (inv_bijection_of (identity A)) (identity A) map_inv_id_id

/- Moving around bijections in equalities -/
@[hott]
def bijection_l_to_r {A : Set} {B : Set} (f : bijection A B) :
  Π {a : A} {b : B}, f a = b -> a = inv_bijection_of f b :=
assume a b p, (inv_bij_l_inv f a)⁻¹ ⬝ ap (inv_bijection_of f) p    

/- The "trivial" characterisation of equalities of sets is by the
   equality of carrier types. This follows because `is_set` is a 
   proposition, hence is an instance of a general scheme, see
   [Rijke-Book, Cor.12.2.4]. -/
local notation `car` A := trunctype.carrier A

@[hott, reducible]
def car_eq_to_set_eq {A B : Set} : ((car A) = car B) -> (A = B) :=
begin
  hinduction A with car_A is_set_A, hinduction B with car_B is_set_B, 
  intro p, fapply apd011 Set.mk, exact p, 
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott]
def car_idp_to_set_idp {A : Set} : 
  car_eq_to_set_eq (idpath (car A)) = idpath A := 
begin 
  hinduction A with car_A is_set_A, change apd011 Set.mk idp _ = _,
  hsimp, change apd011 Set.mk idp idpo = _, refl 
end

@[hott, reducible]
def set_eq_to_car_eq {A B : Set} : (A = B) -> ((car A) = car B) :=
  λ p, ap trunctype.carrier p

@[hott]
def set_eq_equiv_car_eq {A B : Set} : (A = B) ≃ ((car A) = car B) :=
begin
  fapply equiv.mk,
  { exact set_eq_to_car_eq },
  { fapply is_equiv.adjointify,
    { exact car_eq_to_set_eq },
    { hinduction A with car_A is_set_A, hinduction B with car_B is_set_B,
      intro car_eq, change car_A = car_B at car_eq, hinduction car_eq,  
      have q : is_set_A = is_set_B, from is_prop.elim _ _, hinduction q,
      rwr car_idp_to_set_idp },
    { intro p, hinduction p, 
      change car_eq_to_set_eq (ap trunctype.carrier idp) = _,
      rwr ap_idp, rwr car_idp_to_set_idp } }
end   

/- Equalities between two sets also correspond to bijections between the two sets. 
   We construct the equivalence using the Structure Identity Principle
   in [types2]. They do not calculate particularly well when applied to
   identities, but that seems to be a question of making the expressions
   reducible and of using the calculus of equivalences in [init/ua]. -/
@[hott, reducible]
def bij_to_car_eqv {A B : Set} : (bijection A B) -> ((car A) ≃ (car B)) :=
assume f : bijection A B, let f_inv := inv_of_bijection f, g := f_inv.1 in
have c : is_set_inverse_of f g, from f_inv.2,
let f_rinv := @is_set_inverse_of.r_inv _ _ f g c, 
    f_linv := @is_set_inverse_of.l_inv _ _ f g c in
equiv.mk f (is_equiv.adjointify f g f_rinv f_linv)

@[hott]
def Set_dep_ppred (A : Σ (C : Type _), is_set C) : 
  dep_ppred A.1 A.2 :=
begin
  fapply dep_ppred.mk, 
  { fapply ppred.mk, exact λ B : Type _, A.1 = B, refl },
  { intros B is_set_B p, 
    exact Σ (f : bijection (trunctype.mk A.1 A.2) 
                           (trunctype.mk B is_set_B)), 
            (equiv_of_eq p).to_fun = f.map },
  { exact dpair (identity (trunctype.mk A.1 A.2)) idp }
end

@[hott]
def set_sig_eq_equiv_car_eq_bij (A B : Σ C : Type _, is_set C) : 
  (A = B) ≃ (Σ (p : A.1 = B.1), 
                Σ (f : bijection (trunctype.mk A.1 A.2) 
                                 (trunctype.mk B.1 B.2)), 
               (equiv_of_eq p).to_fun = f.map) :=
begin
  hinduction A with car_A is_set_A, 
  fapply @struct_id_char_of_contr (Type _) car_A is_set 
           (is_set_A) (Set_dep_ppred (dpair car_A is_set_A)),
  { exact is_contr_tot_peq car_A },
  { fapply is_contr.mk, 
    exact ⟨is_set_A, (Set_dep_ppred (dpair car_A is_set_A)).dep_base⟩, 
    intro B, hinduction B with is_set_B d, 
    have p : is_set_A = is_set_B, from is_prop.elim _ _,
    hinduction p, fapply sigma.sigma_eq, exact idp,
    apply pathover_idp_of_eq, hsimp, 
    hinduction d with f f_map, fapply sigma.sigma_eq,
    { change identity _ = f, apply bijection_eq_from_map_eq, 
      exact f_map },
    { apply pathover_of_tr_eq, 
      have H : is_set (car_A -> car_A), from 
        @is_set_map _ (trunctype.mk car_A is_set_A),
      exact @is_set.elim _ H _ _ _ _ } }
end

@[hott]
def set_eq_equiv_car_eq_bij (A B : Set) : (A = B) ≃ 
      (Σ (p : (car A) = car B) (f : bijection A B), 
                           (equiv_of_eq p).to_fun = f.map) :=
begin
  hinduction A with car_A is_set_A, hinduction B with car_B is_set_B,
  exact (eq_equiv_fn_eq_of_equiv Set_str_equiv_sig 
                                 (trunctype.mk car_A is_set_A) 
                                 (trunctype.mk car_B is_set_B)) ⬝e
        (set_sig_eq_equiv_car_eq_bij (dpair car_A is_set_A)
                                     (dpair car_B is_set_B))
end

@[hott]
def set_eq_to_car_eq_bij_id (A : Set) : 
  (set_eq_equiv_car_eq_bij A A) (idpath A) = 
                      ⟨idpath (car A), ⟨identity A, idpath id⟩⟩ :=
begin
  change (set_eq_equiv_car_eq_bij A A).to_fun _ = _,
  hinduction A with car_A is_set_A,   
  change ((eq_equiv_fn_eq_of_equiv Set_str_equiv_sig 
                                 (trunctype.mk car_A is_set_A) 
                                 (trunctype.mk car_A is_set_A)) ⬝e
        (set_sig_eq_equiv_car_eq_bij (dpair car_A is_set_A)
                                     (dpair car_A is_set_A))).to_fun _ = _,
  rwr to_fun_trans
end

@[hott]
def car_eq_bij_equiv_bij (A B : Set) : (Σ (p : (car A) = car B) 
      (f : bijection A B), (equiv_of_eq p).to_fun = f.map) ≃
      bijection A B :=
begin
  fapply equiv.mk, 
  { intro eq_bij_eq, exact eq_bij_eq.2.1 },
  { fapply is_equiv.adjointify,
    { intro f, fapply dpair,
      { exact ua (bij_to_car_eqv f) },
      { apply dpair f, rwr equiv_of_eq_ua } },
    { intro b, refl },
    { intro eq_bij_eq, hinduction eq_bij_eq with p bij_eq, 
      hinduction bij_eq with f map_eq, 
      fapply @sigma2_eq' _ _ (λ p (f : bijection A B), 
                                     (equiv_of_eq p).to_fun = f.map),
      { hsimp, rwr <- ua_equiv_of_eq p, apply ap ua, 
        apply equiv_eq', rwr map_eq },
      { refl },
      { exact is_set.elim _ _ } } }       
end

@[hott]
def car_eq_bij_to_bij_id (A : Set) : 
  (car_eq_bij_equiv_bij A A) ⟨idp, ⟨identity A, idpath (@id (car A))⟩⟩ =
  identity A := idp 

@[hott, reducible]
def set_eq_equiv_bij {A B : Set} : (A = B) ≃ (bijection A B) :=
  (set_eq_equiv_car_eq_bij A B) ⬝e (car_eq_bij_equiv_bij A B)

@[hott, reducible]
def set_eq_to_bij {A B : Set} : A = B -> (bijection A B) :=
  equiv.to_fun set_eq_equiv_bij

@[hott, reducible]
def bij_to_set_eq {A B : Set} : (bijection A B) -> A = B :=
  (equiv.to_fun set_eq_equiv_bij)⁻¹ᶠ

@[hott]
def identity_to_idp {A : Set} : bij_to_set_eq (identity A) = idpath A :=
begin
  change (equiv.to_fun ((set_eq_equiv_car_eq_bij A A) ⬝e 
                             (car_eq_bij_equiv_bij A A)))⁻¹ᶠ _ = _,
  rwr to_inv_trans, rwr <- car_eq_bij_to_bij_id A,
  change ((set_eq_equiv_car_eq_bij A A).to_fun)⁻¹ᶠ 
                             ((car_eq_bij_equiv_bij A A)⁻¹ᶠ _) = _, 
  rwr to_left_inv (car_eq_bij_equiv_bij A A),
  rwr <- to_left_inv (set_eq_equiv_car_eq_bij A A) (idpath A), 
  apply ap ((set_eq_equiv_car_eq_bij A A).to_fun)⁻¹ᶠ, 
  rwr set_eq_to_car_eq_bij_id
end     

@[hott]
def idp_to_identity {A : Set} : set_eq_to_bij (idpath A) = identity A :=
begin
  change (equiv.to_fun ((set_eq_equiv_car_eq_bij A A) ⬝e 
                             (car_eq_bij_equiv_bij A A))) _ = _,
  rwr to_fun_trans, rwr set_eq_to_car_eq_bij_id
end 

@[hott]
def right_inv_set_eq_bij {A B : Set} (f : bijection A B) :
  set_eq_to_bij (bij_to_set_eq f) = f := 
@is_equiv.right_inv (A = B) (bijection A B) set_eq_to_bij _ f

@[hott]
def hom_eq_tr_eq {A B : Set} (e : A = B) :
  forall a : A, set_eq_to_bij e a = e ▸ a :=
begin 
  intro a, hinduction e, rwr idp_tr, 
  exact ap10 (ap bijection.map idp_to_identity) a
end   

@[hott]
def bij_hom_tr_eq {A B : Set} (f : bijection A B) : 
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
def set_po_eq {A : Type _} {B : A -> Set} {a₁ a₂ : A} {p : a₁ = a₂} {b₁ : B a₁} {b₂ : B a₂}
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

@[hott, instance]
def dprod_of_Sets_is_set' (A : Type _) (B : A -> Type _) [HA : is_set A] 
  [HB : Π a : A, is_set (B a)] : is_set (Σ (a : A), B a) :=
dprod_of_Sets_is_set (trunctype.mk A HA) (λ a : A, trunctype.mk (B a) (HB a))

@[hott]
def dprod_Set (A : Set) (B : A -> Set) : Set :=
  Set.mk (Σ (a : A), B a) (dprod_of_Sets_is_set A B)   

/- The sum of sets is a set. This is contained in the file [types.sum] of the HoTT3 library
   which does not compile. -/
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

end set

end hott