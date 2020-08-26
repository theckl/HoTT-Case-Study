import types.sigma types.trunc

namespace set

open is_trunc eq sigma sigma.ops trunc equiv is_equiv function

/- We need the empty set, the identity map between sets and some properties of maps between sets. They can be 
   derived from properties of general (n-)types, in [function], but we give them separate definitions adapted 
   to sets, to make them more accessible. -/

definition empty_Set : Set := 
  Set.mk empty (is_trunc_succ empty -1)

definition id_map (A : Set) : A -> A :=
  (id : A -> A) 

lemma id_map_is_right_neutral {A B : Set} (map : A -> B) :
  map ∘ (id_map A) = map :=
by esimp

definition is_set_injective [class] {A B : Set} (f : B -> A) := forall b1 b2 : B, f b1 = f b2 -> b1 = b2

/- The next 2 lemmas should be (and are?) in one of the trunc-files. -/
lemma is_prop_map {A B : Type} (pB : is_prop B) : is_prop (A -> B) :=
have eq_map : forall f1 f2 : A -> B, f1 = f2, from take f1 f2, 
  have map_hom : f1 ~ f2, from take a, is_prop.elim _ _, eq_of_homotopy map_hom,
is_prop.mk eq_map 

lemma is_prop_dprod {A : Type} {P : A -> Type} (pP : forall a : A, is_prop (P a)) : 
  is_prop (forall a : A, P a) :=
have eq_prod : forall dP1 dP2 : (forall a : A, P a), dP1 = dP2, from 
  take dP1 dP2, have dP_hom : dP1 ~ dP2, from take a, have is_prop (P a), from pP a, is_prop.elim _ _, 
  eq_of_homotopy dP_hom,
is_prop.mk eq_prod  

/- Maps between two given sets are sets. 
   Looks like a HoTT-ism, but is actually a rule to construct sets from known sets. -/
lemma is_set_map {A B : Set} : is_set (A -> B) :=
have H : forall (f g : A -> B) (p q : f = g), p = q, from
  take f g p q, 
  have eq_eqv_hom : (f = g) ≃ (f ~ g), from eq_equiv_homotopy, /- uses function extensionality -/
  have is_prop_hom : is_prop (f ~ g), from 
    have pP : forall a : A, is_prop (f a = g a), from take a, is_trunc_eq -1 (f a) (g a),
    is_prop_dprod pP,
  have H_eqv : is_prop (f = g), from is_trunc_is_equiv_closed -1 (equiv.to_fun eq_eqv_hom)⁻¹,
  is_prop.elim p q, 
is_set.mk (A -> B) H

/- That is a HoTT-ism, but should be automatable. -/
lemma is_set_inj_is_prop [instance] {A B : Set} (f : B -> A): is_prop (is_set_injective f) := 
have eq_imp : forall b1 b2 : B, is_prop (f b1 = f b2 -> b1 = b2), from take b1 b2,
  is_prop_map (is_trunc_eq -1 b1 b2),
have eq_b2 : forall b1 : B, is_prop (forall b2 : B, f b1 = f b2 -> b1 = b2), from
  take b1, is_prop_dprod (eq_imp b1),
is_prop_dprod eq_b2

/- fibers of injective maps only contain one element. -/
theorem set_inj_implies_unique_fib {A B : Set} (f : B -> A) : 
  is_set_injective f -> forall a : A, is_prop (fiber f a) :=
take f_inj a,
have H : forall fb1 fb2 : fiber f a, fb1 = fb2
  | (fiber.mk b1 e1) (fiber.mk b2 e2) :=    
    have eqb : b1 = b2, from f_inj b1 b2 (e1 ⬝ e2⁻¹),
    have eqbeq : e1 =[eqb] e2, from pathover_of_tr_eq (is_set.elim _ _),
    apd011 fiber.mk eqb eqbeq, 
is_prop.mk H 

/- This is the universal property of injective maps. -/
lemma univ_prop_of_inj {A B : Set} (i : A -> B) (i_inj : is_set_injective i) : 
  forall (C : Set) (f g : C -> A), i ∘ f = i ∘ g -> f = g :=
take C f g comp_eq, 
have i_hom : forall c : trunctype.carrier C, i (f c) = i (g c), from take c,
  calc i (f c) = (i ∘ f) c : by esimp
           ... = (i ∘ g) c : by rewrite comp_eq
           ... = i (g c) : by esimp,  
have hom : f ~ g, from take c, i_inj (f c) (g c) (i_hom c),         
eq_of_homotopy hom  

definition is_set_surjective [class] {A B : Set} (f : B -> A) := forall a : A, image f a

lemma is_set_surj_is_prop [instance] {A B : Set} (f : B -> A): is_prop (is_set_surjective f) :=
have forall a : A, is_prop (image f a), from _, 
is_prop_dprod _ 

structure is_set_bijective [class] {A B : Set} (f : B -> A) := 
 (inj : is_set_injective f) (surj : is_set_surjective f)

lemma is_set_bij_is_prop [instance] {A B : Set} (f : B -> A) : is_prop (is_set_bijective f) :=
have H : forall bij1 bij2 : is_set_bijective f, bij1 = bij2
     | (is_set_bijective.mk inj1 surj1) (is_set_bijective.mk inj2 surj2) := 
       ap011 is_set_bijective.mk (is_prop.elim inj1 inj2)(is_prop.elim surj1 surj2), 
is_prop.mk H

/- Bijective maps, bundled up. -/
structure bijection (A B : Set) :=
  (map: A -> B) (bij : is_set_bijective map)

attribute bijection.map [coercion]
attribute bijection.bij [instance]

lemma bijection_eq_from_map_eq {A B : Set} : 
  forall f g : bijection A B, bijection.map f = bijection.map g -> f = g  
| (bijection.mk map1 bij1) (bijection.mk map2 bij2) := 
   take map_eq, 
   have tr_eq : map_eq ▸ bij1 = bij2, from
     is_prop.elim (map_eq ▸ bij1) (bij2), 
   have is_bij_eq : bij1 =[map_eq] bij2, from pathover_of_tr_eq tr_eq,
   apd011 bijection.mk map_eq is_bij_eq

lemma map_eq_from_bijection_eq {A B : Set} :
  forall f g : bijection A B, f = g -> bijection.map f = bijection.map g :=
take f g map_eq, ap bijection.map map_eq

/- Note that equality of two bijections and equality of the two underlying sets
   are propositions (not proven), so constructing an equivalence is useless. 
   Similarly, the idpaths must be mapped to each other. -/

definition is_set_right_inverse_of {A B : Set} (f : A -> B) (g : B -> A) :=
  forall b, f (g b) = b

definition is_set_left_inverse_of {A B : Set} (f : A -> B) (g : B -> A) :=
  forall a, g (f a) = a

structure is_set_inverse_of [class] {A B : Set} (f : A -> B) (g : B -> A) := 
  (r_inv : is_set_right_inverse_of f g) (l_inv : is_set_left_inverse_of f g)

lemma id_is_inv_to_id (A : Set) : is_set_inverse_of (id_map A) (id_map A) :=
  let i := id_map A in
  have r_inv : is_set_right_inverse_of i i, from 
    take a, calc i (i a) = a : by esimp,
  have l_inv : is_set_left_inverse_of i i, from 
    take a, calc i (i a) = a : by esimp,
  is_set_inverse_of.mk r_inv l_inv

/- The inverse is uniquely determined. -/
lemma inv_is_unique {A B : Set} (f : A -> B) (g : B -> A) (g' : B -> A) :
  is_set_inverse_of f g -> is_set_inverse_of f g' -> g = g' :=
take inv_g inv_g', 
have hom : g ~ g', from take b,
  calc g b = g (f (g' b)) : is_set_inverse_of.r_inv f g' b
       ... = g' b : is_set_inverse_of.l_inv f g (g' b),
eq_of_homotopy hom /- here, function extensionality is used -/

/- Constructing the inverse of a bijection -/
definition inv_of_bijection [reducible] {A B : Set} (f : bijection A B) : Σ (g : B -> A), is_set_inverse_of f g :=
  let f_inj := is_set_bijective.inj f, f_surj := is_set_bijective.surj f in
  have inv_f : forall b : B, fiber f b, from take b, 
    have fp : is_prop (fiber f b), from set_inj_implies_unique_fib _ (f_inj) _, 
    untrunc_of_is_trunc (f_surj b),
  let g := λ b : B, fiber.point (inv_f b) in
  have r_inv_f : is_set_right_inverse_of f g, from take b, fiber.point_eq (inv_f b),
  have l_inv_f : is_set_left_inverse_of f g, from take a,
    have fpa : is_prop (fiber f (f a)), from set_inj_implies_unique_fib _ (f_inj) _, 
    ap fiber.point (is_prop.elim (inv_f (f a)) (fiber.mk a (idpath (f a)))),
  sigma.mk g (is_set_inverse_of.mk r_inv_f l_inv_f)      

/- Functions with inverses are bijective. -/
definition has_inverse_to_bijection [reducible] {A B : Set} (f : A -> B) (g : B -> A) :
  is_set_inverse_of f g -> bijection A B :=
take inv_f_g,
have f_inj : is_set_injective f, from take a1 a2 feq,
  calc a1 = g (f a1) : by rewrite (is_set_inverse_of.l_inv f g a1)
      ... = g (f a2) : by rewrite feq
      ... = a2 : by rewrite -(is_set_inverse_of.l_inv f g a2) at {2},
have f_surj : is_set_surjective f, from take b, 
  have af : fiber f b, from fiber.mk (g b) (is_set_inverse_of.r_inv f g b),
  tr af,
have is_bij : is_set_bijective f, from is_set_bijective.mk f_inj f_surj,
bijection.mk f is_bij

/- The inverse of a bijectionis a bijection. -/
lemma set_inv_inv {A B : Set} (f : A -> B) (g : B -> A) :
  is_set_inverse_of f g -> is_set_inverse_of g f :=
take inv_f_g,
is_set_inverse_of.mk (is_set_inverse_of.l_inv f g) (is_set_inverse_of.r_inv f g)

definition inv_bijection_of [reducible] {A B : Set} (f : bijection A B) : bijection B A :=
  let g := (inv_of_bijection f).1, inv_f_g := (inv_of_bijection f).2 in
  has_inverse_to_bijection g f (set_inv_inv f g inv_f_g)

lemma inv_bij_is_inv {A B : Set} (f : bijection A B) :
  is_set_inverse_of f (inv_bijection_of f) := 
(inv_of_bijection f).2

/- The identity map is a bijection. -/
definition identity (A : Set) : bijection A A := 
  let i := id_map A in
  have id_inv : is_set_inverse_of i i, from id_is_inv_to_id A, 
  has_inverse_to_bijection i i id_inv

lemma identity_to_id_map (A : Set) :
  bijection.map (identity A) = id_map A :=
by esimp

/- The inverse of the identity map is the identity map itself. -/
lemma inv_bij_of_id_id {A : Set} : inv_bijection_of (identity A) = identity A := 
  have map_inv_id_id : inv_bijection_of (identity A) = id_map A, from
    have hom : inv_bijection_of (identity A) ~ id_map A, from take a, by esimp, 
    eq_of_homotopy hom,
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
definition set_eq_to_car_eq {A B : Set} : (A = B) -> ((car A) = (car B)) :=
  take e, ap trunctype.carrier e

definition idp_set_to_idp_car {A : Set} : set_eq_to_car_eq (idpath A) = idpath (car A) :=
  by esimp

definition car_eq_to_set_eq [reducible] : Π {A B : Set}, ((car A) = (car B)) -> (A = B)
  | (Set.mk car1 struct1) (Set.mk car2 struct2) := 
  take ec, 
  have est : struct1 =[ec] struct2, from 
    pathover_of_tr_eq (is_prop.elim (ec ▸ struct1) struct2), 
  apd011 Set.mk ec est 

/- It's complicated to do calculations with [car_eq_to_set_eq].-/
definition idp_car_to_idp_set : Π {A : Set}, car_eq_to_set_eq (idpath (car A)) = idpath A :=
  begin
    intro A,
    cases A with [carr, struct],
    rewrite ↑car_eq_to_set_eq,
    have est_eq : pathover_of_tr_eq (is_prop.elim ((idpath carr) ▸ struct) struct) = idpatho struct, from 
      is_prop.elim (pathover_of_tr_eq _) (idpatho struct),
    rewrite est_eq
  end

lemma linv_set_eq_car_eq {A B : Set} : forall (es : A = B),
  car_eq_to_set_eq (set_eq_to_car_eq es) = es :=
have H : forall (A : Set), car_eq_to_set_eq (set_eq_to_car_eq (idpath A)) = idpath A, from 
  take A,
  calc  car_eq_to_set_eq (set_eq_to_car_eq (idpath A)) = 
              car_eq_to_set_eq (idpath (car A)) : by esimp
        ... = idpath A : idp_car_to_idp_set,
take es, rec_unbased H es

/- This should be shown for general structures consisting of a type and
   a dependent proposition. -/
lemma ap_car_apd011_set_mk {cA cB: Type} :
  Π (ec : cA = cB) [s : is_set cA] [t : is_set cB] (est : s =[ec] t), 
  ap trunctype.carrier (apd011 Set.mk ec est) = ec := 
have H_ec : Π (cA : Type) (s t : is_set cA) (est : s =[idpath cA] t), 
         ap trunctype.carrier (apd011 Set.mk (idpath cA) est) = idpath cA, from
  take cA s t est,
  have H_est : Π (s : is_set cA), 
               ap trunctype.carrier (apd011 Set.mk (idpath cA) (idpatho s)) = idpath cA, from
    take s, by esimp, 
  idp_rec_on est (H_est s), 
take ec, rec_unbased H_ec ec

lemma rinv_set_eq_car_eq : Π {A B : Set}, forall (ec : (car A) = (car B)),
  set_eq_to_car_eq (car_eq_to_set_eq ec) = ec
| (Set.mk carr1 struct1) (Set.mk carr2 struct2) := take ec, 
  let est := pathover_of_tr_eq (is_prop.elim (ec ▸ struct1) struct2) in  
  calc set_eq_to_car_eq (car_eq_to_set_eq ec) = ap trunctype.carrier (car_eq_to_set_eq ec) : 
       by rewrite ↑set_eq_to_car_eq 
       ... = ap trunctype.carrier (apd011 Set.mk ec est) : by rewrite ↑car_eq_to_set_eq
       ... = ec : ap_car_apd011_set_mk ec est

definition set_eq_equiv_car_eq {A B : Set} : (A = B) ≃ ((car A) = (car B)) :=
  equiv.mk set_eq_to_car_eq (adjointify set_eq_to_car_eq car_eq_to_set_eq 
                                        rinv_set_eq_car_eq linv_set_eq_car_eq)

definition car_eq_equiv_car_eqv {A B : Set} : ((car A) = (car B)) ≃ ((car A) ≃ (car B)) :=
  !eq_equiv_equiv     /- Here, univalence is used. -/

definition car_eq_to_car_eqv {A B : Set} : ((car A) = (car B)) -> ((car A) ≃ (car B)) :=
  equiv.to_fun car_eq_equiv_car_eqv

definition car_eqv_to_car_eq {A B : Set} : ((car A) ≃ (car B)) -> ((car A) = (car B)) :=
  (equiv.to_fun car_eq_equiv_car_eqv)⁻¹ 

definition id_map_eqv (A : Set) : (car A) ≃ (car A) :=
  equiv.mk (id_map A) (is_equiv_id (car A))

lemma id_to_id_map_eqv (A : Set) : car_eq_to_car_eqv (idpath (car A)) = id_map_eqv A := 
  by esimp

lemma id_map_eqv_to_id (A : Set) : car_eqv_to_car_eq (id_map_eqv A) = idpath (car A) := 
  calc car_eqv_to_car_eq (id_map_eqv A) = car_eqv_to_car_eq (car_eq_to_car_eqv (idpath (car A))) :
       ap car_eqv_to_car_eq (id_to_id_map_eqv A)
       ... = idpath (car A) : is_equiv.left_inv car_eq_equiv_car_eqv (idpath (car A))

definition car_eqv_to_bij [reducible] {A B : Set} : ((car A) ≃ (car B)) -> (bijection A B) :=
  take f_eqv : (car A) ≃ (car B), 
  let f := equiv.to_fun f_eqv, g := (equiv.to_fun f_eqv)⁻¹ in
  let inv_f_g := is_set_inverse_of.mk (is_equiv.right_inv f_eqv) (is_equiv.left_inv f_eqv) in
  has_inverse_to_bijection f g inv_f_g 

definition bij_to_car_eqv [reducible] {A B : Set} : (bijection A B) -> ((car A) ≃ (car B)) :=
take f : bijection A B, let f_inv := inv_of_bijection f, g := f_inv.1 in
have is_set_inverse_of f g, from f_inv.2,
let f_rinv := is_set_inverse_of.r_inv f g, f_linv := is_set_inverse_of.l_inv f g in
equiv.mk f (adjointify f g f_rinv f_linv)

lemma rinv_set_equiv_bijection {A B : Set} : forall f : bijection A B,
  car_eqv_to_bij (bij_to_car_eqv f) = bijection.map f :=
let F := car_eqv_to_bij, G := bij_to_car_eqv in
take f, have eq_G : equiv.to_fun (G f) = bijection.map f, by esimp,
have eq_F : bijection.map (F (G f)) = equiv.to_fun (G f), by esimp,
eq_F ⬝ eq_G

lemma linv_bijection_set_equiv {A B : Set} : forall e : (car A) ≃ (car B),
  bij_to_car_eqv (car_eqv_to_bij e) = equiv.to_fun e :=
let F := car_eqv_to_bij, G := bij_to_car_eqv in
take e, have eq_F : bijection.map (F e) = equiv.to_fun e, by esimp,
have eq_G : equiv.to_fun (G (F e)) = bijection.map (F e), by esimp,
eq_G ▸ eq_F
  
/- The next 2 lemmas should be in [init.equiv]. -/
definition equiv_eq_from_fun_eq {A B : Type} : forall e1 e2 : A ≃ B, 
  equiv.to_fun e1 = equiv.to_fun e2 -> e1 = e2
| (equiv.mk fun1 is_eqv1) (equiv.mk fun2 is_eqv2) := 
  take fun_eq, 
  have tr_eq : fun_eq ▸ is_eqv1 = is_eqv2, from
     is_prop.elim (fun_eq ▸ is_eqv1) (is_eqv2),
  have is_equiv_eq : is_eqv1 =[fun_eq] is_eqv2, from pathover_of_tr_eq tr_eq,  
  apd011 equiv.mk fun_eq is_equiv_eq

definition fun_eqv_trans_comp_eqv {A B C : Type} : Π (F : A ≃ B) (G : B ≃ C), 
  equiv.to_fun (equiv.trans F G) = (equiv.to_fun G) ∘ (equiv.to_fun F) :=
take F G, by esimp

definition car_eqv_equiv_bij {A B : Set} : ((car A) ≃ (car B)) ≃ (bijection A B) :=
  let F := car_eqv_to_bij, G := bij_to_car_eqv in
  have rinv : forall f, F (G f) = f, from take f, 
    have map_eq : bijection.map (F (G f)) = bijection.map f, from rinv_set_equiv_bijection f,
    bijection_eq_from_map_eq _ _ map_eq, 
  have linv : forall e, G (F e) = e, from take e,
    have fun_eq : equiv.to_fun (G (F e)) = equiv.to_fun e, from linv_bijection_set_equiv e,
    equiv_eq_from_fun_eq _ _ fun_eq, 
  equiv.mk F (adjointify F G rinv linv)

lemma identity_to_id_eqv (A : Set) : bij_to_car_eqv (identity A) = id_map_eqv A := 
  have fun_eq : equiv.to_fun (bij_to_car_eqv (identity A)) = equiv.to_fun (id_map_eqv A), by esimp,
  equiv_eq_from_fun_eq _ _ fun_eq

lemma id_eqv_to_identity (A : Set) : car_eqv_to_bij (id_map_eqv A) = identity A := 
  have map_eq : bijection.map (car_eqv_to_bij (id_map_eqv A)) = bijection.map (identity A), by esimp, 
  bijection_eq_from_map_eq _ _ map_eq

definition set_eq_equiv_bij {A B : Set} : (A = B) ≃ (bijection A B) :=
  (set_eq_equiv_car_eq ⬝e car_eq_equiv_car_eqv) ⬝e car_eqv_equiv_bij

definition set_eq_to_bij {A B : Set} : A = B -> (bijection A B) :=
  equiv.to_fun set_eq_equiv_bij

definition bij_to_set_eq {A B : Set} : (bijection A B) -> A = B :=
  (equiv.to_fun set_eq_equiv_bij)⁻¹ 

/- These equivalence functions extracted from the equivalenc can indeed be used for 
   calculations. -/
lemma identity_to_idp {A : Set} : bij_to_set_eq (identity A) = idpath A :=
calc bij_to_set_eq (identity A) = 
            car_eq_to_set_eq (car_eqv_to_car_eq (bij_to_car_eqv (identity A))) : by esimp
     ... =  idpath A : begin rewrite identity_to_id_eqv, 
                             rewrite id_map_eqv_to_id, 
                             rewrite idp_car_to_idp_set end 

definition right_inv_set_eq_bij {A B : Set} (f : bijection A B) :
  set_eq_to_bij (bij_to_set_eq f) = f :=
@is_equiv.right_inv (A = B) (bijection A B) set_eq_to_bij _ f

corollary hom_eq_tr_eq {A B : Set} (e : A = B) :
  forall a : A, set_eq_to_bij e a = e ▸ a :=
have H : Π (A : Set), forall a : A, set_eq_to_bij idp a = idp ▸ a, from 
  take A a, by esimp,
rec_unbased H e 

corollary bij_hom_tr_eq {A B : Set} (f : bijection A B) : 
  forall a : A, f a = (bij_to_set_eq f) ▸ a := 
let rinv := right_inv_set_eq_bij f, 
    eq_f := bij_to_set_eq f in
take a,  
calc f a = set_eq_to_bij eq_f a : apd10 (ap bijection.map (eq.inverse rinv)) a
     ... = eq_f ▸ a : hom_eq_tr_eq eq_f a 

end set
