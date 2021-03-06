import types.sigma types.trunc set_theory

namespace subset

open is_trunc eq sigma sigma.ops trunc equiv is_equiv function set

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

structure Subset (A : Set) :=
   (carrier : Set) (map : carrier -> A) (inj : is_set_injective map)

attribute Subset.carrier [coercion]
attribute Subset.inj [instance]

definition total_Subset (A : Set) : Subset A := 
  have id_is_inj : is_set_injective (id : A -> A), from take a1 a2 f_eq, 
    calc a1 = id a1 : by esimp
         ... = id a2 : by rewrite f_eq
         ... = a2 : by esimp,
  Subset.mk A (id : A -> A) id_is_inj 

/- The empty set is a subset of every set [A], an elegant consequence of the construction 
   of subsets. -/
definition empty_Subset (A : Set) : Subset A := 
  have f : empty_Set -> A, from take e, empty.elim e,
  have is_inj_f : is_set_injective f, from take e, empty.elim e,
  Subset.mk empty_Set f is_inj_f

/- The image of a map betweens sets is a subset of the codomain. We show this in several steps:
   * First, we show that [total_image] from [function] is a set. This works more generally: 
     A sigma type whose dependent components are sets is a set. It can be shown for n-types 
     using the results in [hit.trunc] on truncations of sigma types. 
   * Second, we construct a map from [total_image] into the codomain and show that it is 
     injective.
   * Now we have all the ingredients to construct the image as a subset of the codomain. -/
definition image_is_set {A B : Set} (f : A -> B) : is_set (total_image f) :=
    have H : forall c d : total_image f, is_prop (c = d), from 
      take c d, 
      have forall p q : c = d, p = q, from 
        take p q, 
        have eq1 : p..1 = q..1, from 
          @is_prop.elim (c.1 = d.1) (is_trunc_eq -1 c.1 d.1) p..1 q..1,  
        have eq2 : p..2 =[eq1] q..2, from 
          have Hchpq : change_path eq1 p..2 = q..2, from 
            let p2 := tr_eq_of_pathover (change_path eq1 p..2),
                q2 := tr_eq_of_pathover q..2 in
            have Heq_pq : p2 = q2, from is_prop.elim p2 q2,
            have H_equiv : equiv (c.2 =[q..1] d.2) (q..1 ▸ c.2 = d.2), from 
              pathover_equiv_tr_eq _ _ _,
            let F := (equiv.to_fun H_equiv)⁻¹, fib := fiber f c.1 in
            have HF : is_equiv F, from is_equiv_inv (equiv.to_fun H_equiv),
            have H_trunc1 : is_prop (q..1 ▸ c.2 = d.2), from 
              have H_prop : is_prop (trunc -1 fib), from is_trunc_trunc -1 _ ,
              have H_set : is_set (trunc -1 fib), from is_trunc_succ _ _,
              !is_trunc_eq,
            have H_trunc2 : is_prop (c.2 =[q..1] d.2), from is_trunc_is_equiv_closed -1 F,
            is_prop.elim (change_path eq1 p..2) q..2,
          pathover_of_change_path eq1 p..2 q..2 Hchpq,
        sigma_eq2 eq1 eq2,
      is_prop.mk this,
    is_trunc_succ_intro (total_image f) -1

definition image_Set {A B : Set} (f : A -> B) := Set.mk (total_image f) (image_is_set f)

definition image_embedding {A B : Set} (f : A -> B) : (image_Set f) -> B :=
  λ (bf : total_image f), bf.1
 
lemma im_emb_is_inj {A B : Set} (f : A -> B) : is_set_injective (image_embedding f) :=
  let im_emb := image_embedding f in
  show forall (bf1 bf2 : total_image f), im_emb bf1 = im_emb bf2 -> bf1 = bf2
  | (sigma.mk b1 f1) (sigma.mk b2 f2) :=
    take (im_emb_eq : b1 = b2), 
    have tr_eq : im_emb_eq ▸ f1 = f2, from !is_prop.elim,
    have fib_eq : f1 =[im_emb_eq] f2, from pathover_of_tr_eq tr_eq,
    apd011 sigma.mk im_emb_eq fib_eq 

definition Image {A B : Set} (f : A -> B) : Subset B :=
  Subset.mk (image_Set f) (image_embedding f) (im_emb_is_inj f)

lemma ap_car_ap_sset_mk {A : Set} (carB : Set) (mapB : carB -> A) 
  {inj1 inj2 : is_set_injective mapB} (inj_eq : inj1 = inj2) : 
  ap Subset.carrier (ap (Subset.mk carB mapB) inj_eq) = idpath carB :=
have H : Π (inj1 : is_set_injective mapB), 
         ap Subset.carrier (ap (Subset.mk carB mapB) (idpath inj1)) = idpath carB, from
  take inj1, 
    by esimp,
rec_unbased H inj_eq

/- The type of subsets of [A] is a set: the power set. 
   To show this we first characterize equalities of subsets : they correspond to
   bijetions of the underlying sets compatible with the inclusion maps.
   The core of the construction of this equivalence is that there may be many bijections 
   between the underlying sets, but the compatibility makes the bijection unique. -/
definition sset_bijection [reducible] {A : Set} (B C : Subset A) :=
  Σ (f : bijection B C), (Subset.map C) ∘ (bijection.map f) = (Subset.map B) 

definition sset_identity [reducible] {A : Set} : Π (B : Subset A), sset_bijection B B 
| (Subset.mk carB mapB injB) :=
  have bij_comp : mapB ∘ (bijection.map (identity carB)) = mapB, from 
    calc mapB ∘ (bijection.map (identity carB)) = mapB ∘ (id_map carB) : identity_to_id_map carB
         ... = mapB : id_map_is_right_neutral mapB,
  sigma.mk (identity carB) bij_comp 

lemma sset_ident_to_ident {A : Set} : Π (B : Subset A),
  (sset_identity B).1 = identity (Subset.carrier B)
| (Subset.mk carB mapB injB) :=
  by esimp

lemma bij_eq_bij_comp_eq {A : Set} {B C : Subset A} : 
  forall fc gc : sset_bijection B C, fc.1 = gc.1 -> fc = gc :=
take fc gc bij_eq, 
have tr_eq : bij_eq ▸ fc.2 = gc.2, from is_prop.elim (bij_eq ▸ fc.2) gc.2,
have comp_eq : fc.2 =[bij_eq] gc.2, from pathover_of_tr_eq tr_eq,
sigma_eq bij_eq comp_eq

definition sset_eq_to_bij {A : Set} {B C : Subset A} : 
  B = C -> sset_bijection B C := 
take eq,
have H : Π (B : Subset A), sset_bijection B B, from
  take B, sset_identity B,
rec_unbased H eq

lemma sset_id_to_identity {A : Set} {B : Subset A} :
  sset_eq_to_bij (idpath B) = sset_identity B :=
by esimp

/- Should be in [init.path] with [A], [B], [C] types, but the elaborator can't handle it. -/
 lemma tr_fun_ext {A B C : Set} (p : A = B) : 
  forall (h : B -> C) (a : A), (p⁻¹ ▸ h) a = h (p ▸ a) :=
have H : Π (A : Set), forall (h : A -> C) (a : A), (idp⁻¹ ▸ h) a = h (idp ▸ a), 
  begin intros, esimp end, 
rec_unbased H p

/- Equalities of a structure like [Subset] consisting of 3 dependent fields are difficult to handle. 
   We need some auxiliary definitions and lemmas focussing on [Subset]-structures constructed with
   [Subset.mk] - they will be used in inductive arguments. -/
definition bij_to_sset_map_eq [reducible] {A : Set} : Π {B C : Subset A} (ss_bij : sset_bijection B C),
  Subset.map B =[bij_to_set_eq ss_bij.1] Subset.map C
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  take ss_bij,
  show mapB =[bij_to_set_eq ss_bij.1] mapC, from
  let f := ss_bij.1, car_eq := bij_to_set_eq f in
  let tr_map_C := car_eq⁻¹ ▸ mapC, fm := bijection.map f in 
  have comp : mapC ∘ fm = mapB, from ss_bij.2,
  have comp_hom : tr_map_C ~ mapC ∘ fm, from take b,
    calc tr_map_C b = mapC (car_eq ▸ b) : tr_fun_ext car_eq mapC b
         ... = mapC (fm b) : bij_hom_tr_eq f b,
  pathover_of_eq_tr (comp⁻¹ ⬝ (eq_of_homotopy comp_hom)⁻¹)

definition sset_comp_eq {A : Set} (car1 car2 : Set) (map1 : car1 -> A) (map2 : car2 -> A) :=
  Σ (car_eq : car1 = car2), map1 =[car_eq] map2

/- This is a subtle point: The equality of maps induced by the equality of subsets is
   already induced by the induced equality of carrier sets. This can be shown using
   [pathover_ap] in [init.pathover]. -/
definition sset_mk_eq_to_comp_eq {A : Set} {car1 car2 : Set} 
  {map1 : car1 -> A} {map2 : car2 -> A}
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2] : 
  (Subset.mk car1 map1 inj1 = Subset.mk car2 map2 inj2) -> 
    (sset_comp_eq car1 car2 map1 map2) :=
take mk_eq, let car_eq := ap Subset.carrier mk_eq in
have map_mk_eq : map1 =[mk_eq] map2, from apd Subset.map mk_eq,
have map_car_eq : map1 =[car_eq] map2, from 
  pathover_ap (λ (carr : Set), carr -> A) Subset.carrier map_mk_eq,
dpair car_eq map_car_eq

definition sset_comp_eq_to_mk_eq [reducible] {A : Set} {car1 car2 : Set} :
  Π (car_eq : car1 = car2) 
  {map1 : car1 -> A} {map2 : car2 -> A} (map_eq : map1 =[car_eq] map2) 
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2],  
  Subset.mk car1 map1 inj1 = Subset.mk car2 map2 inj2 := 
take car_eq map1 map2 map_eq,
have Hm : Π (inj1 inj2: is_set_injective map1),
            Subset.mk car1 map1 inj1 = Subset.mk car1 map1 inj2, from 
  take inj1 inj2, 
  ap (Subset.mk car1 map1) (is_prop.elim inj1 inj2),
pathover.cases_on map_eq Hm

definition sset_comp_eq_to_sset_eq [reducible] {A : Set} : Π {B C : Subset A}
  (car_eq : Subset.carrier B = Subset.carrier C) 
  (map_eq : Subset.map B =[car_eq] Subset.map C), 
  B = C 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  take car_eq map_eq,
  sset_comp_eq_to_mk_eq car_eq map_eq

definition ap_sset_comp_to_car [reducible] {A : Set} {car1 car2 : Set} :
  Π (car_eq : car1 = car2) 
  {map1 : car1 -> A} {map2 : car2 -> A} (map_eq : map1 =[car_eq] map2) 
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2],
  ap Subset.carrier (sset_comp_eq_to_mk_eq car_eq map_eq) = car_eq :=
take car_eq,
have Hc : Π (car1 : Set) (map1 map2 : car1 -> A) (map_eq : map1 =[idpath car1] map2)
          [inj1 : is_set_injective map1] [inj2 : is_set_injective map2],
          ap Subset.carrier (sset_comp_eq_to_mk_eq (idpath car1) map_eq) = idpath car1, from
  take car1 map1 map2 map_eq, 
  have Hm : Π (inj1 inj2: is_set_injective map1),
            ap Subset.carrier (@sset_comp_eq_to_mk_eq _ _ _ (idpath car1) _ _ (idpatho map1) inj1 inj2) = idpath car1, from
    take inj1 inj2, 
    have eq1 : @sset_comp_eq_to_mk_eq _ _ _ (idpath car1) _ _ (idpatho map1) inj1 inj2 = 
                   ap (Subset.mk car1 map1) (is_prop.elim inj1 inj2), by esimp,
    begin rewrite eq1, rewrite (ap_car_ap_sset_mk car1 map1 (is_prop.elim inj1 inj2)) end,
  pathover.cases_on map_eq Hm, 
rec_unbased Hc car_eq

/- We can only prove this equality because we defined [sset_comp_eq_to_mk_eq] 
   inductively. -/
definition idp_comp_to_sset_id {A : Set} : Π (B : Subset A), 
  sset_comp_eq_to_sset_eq (idpath (Subset.carrier B)) (idpatho (Subset.map B)) = 
  idpath B 
| (Subset.mk carB mapB injB) := 
  have inj_eq_eq : is_prop.elim injB injB = idpath injB, from !is_set.elim,
calc sset_comp_eq_to_sset_eq (idpath carB) (idpatho mapB) = 
           sset_comp_eq_to_mk_eq (idpath carB) (idpatho mapB) : 
     begin rewrite ↑sset_comp_eq_to_sset_eq, reflexivity end
     ... = ap (Subset.mk carB mapB) (is_prop.elim injB injB) : 
     begin rewrite ↑sset_comp_eq_to_mk_eq, reflexivity end
     ... = ap (Subset.mk carB mapB) (idpath injB) : 
     begin rewrite inj_eq_eq, reflexivity end    
     ... = idpath (Subset.mk carB mapB injB) : 
     begin esimp, reflexivity end

definition bij_to_sset_eq [reducible] {A : Set}: Π {B C : Subset A}, 
  sset_bijection B C -> B = C 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) := 
  take comp_bij, let f := comp_bij.1 in 
  let car_eq := bij_to_set_eq f,
      map_eq := bij_to_sset_map_eq comp_bij in
  sset_comp_eq_to_mk_eq car_eq map_eq

lemma bij_to_sset_eq_unf_eq {A : Set} : Π {B C : Subset A}
  (sset_bij : sset_bijection B C), 
  bij_to_sset_eq (sset_bij) = sset_comp_eq_to_sset_eq (bij_to_set_eq sset_bij.1) (bij_to_sset_map_eq sset_bij) 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  take sset_bij,
  let car_eq := bij_to_set_eq sset_bij.1, 
      map_eq := bij_to_sset_map_eq sset_bij in
  calc bij_to_sset_eq (sset_bij) = sset_comp_eq_to_mk_eq car_eq map_eq : by rewrite ↑bij_to_sset_eq
       ... = sset_comp_eq_to_sset_eq car_eq map_eq : by rewrite ↑sset_comp_eq_to_sset_eq 

lemma identity_to_sset_id {A : Set} : Π (B : Subset A),
  bij_to_sset_eq (sset_identity B) = idpath B := 
take B,
let carB := Subset.carrier B, mapB := Subset.map B,
    injB := Subset.inj B in 
let f := (sset_identity B).1 in
let car_eq := bij_to_set_eq f in
have car_eq_idp : car_eq = idpath carB, from 
  calc car_eq = bij_to_set_eq (identity carB) : sset_ident_to_ident
       ... = idpath carB : identity_to_idp,
let map_eq := bij_to_sset_map_eq (sset_identity B) in
have map_eq_eqv : (mapB =[idpath carB] mapB) ≃ (mapB = mapB), from 
  pathover_idp mapB mapB,
have is_set (carB -> A), from is_set_map,
have prop_map_eq : is_prop (mapB =[idpath carB] mapB), from 
  is_trunc_equiv_closed_rev -1 map_eq_eqv,
have change_po : change_path car_eq_idp map_eq = idpatho mapB, from !is_prop.elim,
have map_eq_idpo : map_eq =[car_eq_idp] idpatho mapB, from 
  pathover_of_change_path car_eq_idp map_eq (idpatho mapB) change_po,
have unf_eq : bij_to_sset_eq (sset_identity B) = sset_comp_eq_to_sset_eq car_eq map_eq, from
  bij_to_sset_eq_unf_eq (sset_identity B),
calc bij_to_sset_eq (sset_identity B) = sset_comp_eq_to_sset_eq car_eq map_eq : by rewrite unf_eq
     ... = sset_comp_eq_to_sset_eq (idpath carB) (idpatho mapB) : 
     apd011 (λ (eq1 : carB = carB) (eq2 : mapB =[eq1] mapB), sset_comp_eq_to_sset_eq eq1 eq2) 
            car_eq_idp map_eq_idpo
     ... = idpath B : idp_comp_to_sset_id B

lemma sset_bij_eq_set_bij {A : Set} (B C : Subset A) : forall e : B = C, 
  (sset_eq_to_bij e).1 = set_eq_to_bij (ap Subset.carrier e) := 
have H : Π (B : Subset A), (sset_eq_to_bij (idpath B)).1 = set_eq_to_bij (ap Subset.carrier idp), from
  take B, calc (sset_eq_to_bij (idpath B)).1 = (sset_identity B).1 : by esimp
               ... = identity (Subset.carrier B) : sset_ident_to_ident
               ... = set_eq_to_bij (ap Subset.carrier idp) : by esimp,
take e, rec_unbased H e

lemma bij_sset_eq_bij_set {A : Set} : forall (B C : Subset A)  
  (sset_bij : sset_bijection B C) (b : Subset.carrier B), 
  ap Subset.carrier (bij_to_sset_eq sset_bij) ▸ b = bij_to_set_eq sset_bij.1 ▸ b 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) := 
  take sset_bij b, 
  let ss_eq := bij_to_sset_eq sset_bij, 
      car_eq := bij_to_set_eq sset_bij.1,
      map_eq := bij_to_sset_map_eq sset_bij in
  have eq1 : ss_eq = sset_comp_eq_to_mk_eq car_eq map_eq, by esimp,
  have eq2 : ap Subset.carrier (sset_comp_eq_to_mk_eq car_eq map_eq) = car_eq, from 
    ap_sset_comp_to_car car_eq map_eq,
  begin rewrite eq1, rewrite eq2 end

lemma sset_eq_equiv_bij {A : Set} (B C : Subset A) : 
  B = C ≃ sset_bijection B C := 
have rinv : forall fc, sset_eq_to_bij (bij_to_sset_eq fc) = fc, from 
  let F := @sset_eq_to_bij A B C, G := @bij_to_sset_eq A B C in
  take fc, let f := fc.1, FGf := (F (G fc)).1 in 
  have bijmap_hom : bijection.map FGf ~ bijection.map f, from 
    take b, 
    calc bijection.map FGf b = bijection.map (set_eq_to_bij (ap Subset.carrier (G fc))) b : 
                               apd10 (ap bijection.map (sset_bij_eq_set_bij B C (G fc))) b
                         ... = (ap Subset.carrier (G fc)) ▸ b : hom_eq_tr_eq (ap Subset.carrier (G fc)) b
                         ... = (bij_to_set_eq f) ▸ b : bij_sset_eq_bij_set B C fc b
                         ... = (bijection.map f) b : bij_hom_tr_eq f b,
  have bij_eq : FGf = f, from
    have bijmap_eq : bijection.map FGf = bijection.map f, from
      eq_of_homotopy bijmap_hom,
    bijection_eq_from_map_eq _ _ bijmap_eq,
  bij_eq_bij_comp_eq _ _ bij_eq,
have linv : forall e, bij_to_sset_eq (sset_eq_to_bij e) = e, from 
  have H : forall (B : Subset A), bij_to_sset_eq (sset_eq_to_bij (idpath B)) = idpath B, from take B,   
    calc bij_to_sset_eq (sset_eq_to_bij (idpath B)) = bij_to_sset_eq (sset_identity B) : sset_id_to_identity
         ... = idpath B : identity_to_sset_id,
  take e, rec_unbased H e,
equiv.mk sset_eq_to_bij (adjointify sset_eq_to_bij bij_to_sset_eq rinv linv)

theorem Powerset_is_set {A : Set} : is_set (Subset A) := 
have H_eq : forall B C : Subset A, is_prop (B = C), from take B C,
  let mapB := Subset.map B, mapC := Subset.map C in
  have bij_eq_is_prop : is_prop (sset_bijection B C), from 
    have H_bij_eq : forall (beq1 beq2 : sset_bijection B C), beq1 = beq2, 
      from take beq1 beq2,
      let f := beq1.1, g := beq2.1 in  
      have p_map : (bijection.map f) = (bijection.map g), from 
        have i_comp_eq : mapC ∘ f = mapC ∘ g, from 
          calc mapC ∘ f = mapB : by exact beq1.2
               ... = mapC ∘ g : by exact (beq2.2)⁻¹, 
        univ_prop_of_inj mapC (Subset.inj C) (Subset.carrier B) f g i_comp_eq, 
      have p : f = g, from bijection_eq_from_map_eq f g p_map,
      have tr_eq : p ▸ beq1.2 = beq2.2, from is_prop.elim (p ▸ beq1.2) beq2.2,
      have q : beq1.2 =[p] beq2.2, from pathover_of_tr_eq tr_eq,  
      sigma_eq p q,
    is_prop.mk H_bij_eq, 
  is_trunc_is_equiv_closed -1 (equiv.to_fun (sset_eq_equiv_bij B C))⁻¹,
is_trunc_succ_intro (Subset A) -1 

definition Powerset (A : Set) : Set :=
  Set.mk (Subset A) Powerset_is_set

/- Subsets of [A : Set] can also be defined by predicates [P : A -> Prop]. Vice versa,  
   predicates can be extracted from a subset of [A]; this yields an equivalence.
   The subset defined by a predicate uses a bundled version of the [subtype] in [types.sigma].
   TODO: Introduce the standard notation {x : A | P a} for subsets given by predicates
         overwriting the notation for subtypes. -/
definition Setpred (A : Set) := A -> Prop.{0} 
/- The 0 sorts out universe troubles. It can be replaced by 1. 
   I don't know whether it causes troubles when constructing predicates;
   this is connected to propositional resizing. -/

definition sset_to_pred {A : Set} : Π (B : Subset A), Setpred A :=
  take B, λ (a : A), image (Subset.map B) a

lemma is_set_pred {A : Set} : Π (pred : Setpred A), is_set (Σ (a : A), pred a) :=
  take pred, 
  have forall (a : A), is_set (pred a), from 
    take a, have is_prop (pred a), from trunctype.struct (pred a),
    is_trunc_succ (pred a) -1, 
  is_trunc_sigma pred 0

/- Should be in one of the library files on the sigma type.
   [subtype_eq] is the subtype-version in [types.sigma]. -/
lemma sigma_prop_pr1_inj {A : Type} {B : A -> Prop} :
  forall (b c : Σ (a : A), B a), b.1 = c.1 -> b = c :=
take b c pr1_eq,
have pr2_tr : pr1_eq ▸ b.2 = c.2, from !is_prop.elim, 
have pr2_eq : b.2 =[pr1_eq] c.2, from pathover_of_tr_eq pr2_tr,
sigma_eq pr1_eq pr2_eq

/- We construct carrier, map and a proof of injectivity of the subset defined 
   by a predicate separately, to be able to use these components in later calculations. -/
definition pred_to_sset_car [reducible] {A : Set} (pred : Setpred A) : Set :=
  let predset := Σ (a : A), trunctype.carrier (pred a)  in
  Set.mk predset (is_set_pred pred)  

definition pred_to_sset_map [reducible] {A : Set} (pred : Setpred A) :
  pred_to_sset_car pred -> A :=
let carr := pred_to_sset_car pred in
λ (b : carr), b.1 

definition pred_to_sset_inj [reducible] {A : Set} (pred : Setpred A) :
  is_set_injective (pred_to_sset_map pred) := 
let map := pred_to_sset_map pred in
take b1 b2 map_eq, 
have map_eq_b : (b1).1 = (b2).1, from
  calc (b1).1 = map b1 : by esimp
       ... = map b2 : map_eq
       ... = (b2).1 : by esimp,
sigma_prop_pr1_inj b1 b2 map_eq_b

definition pred_to_sset [reducible] {A : Set} (pred : Setpred A) : 
  Subset A :=
Subset.mk (pred_to_sset_car pred) (pred_to_sset_map pred) (pred_to_sset_inj pred)

definition pred_to_im {A : Set} (pred : Setpred A) (a : A) : 
  pred a -> image (Subset.map (pred_to_sset pred)) a :=
let B := pred_to_sset pred,
    mapB := Subset.map B in
take p, let apr := dpair a p in /- an element in [predset] -/
have im_a : mapB apr = a, by esimp, /- mapped to a -/
have fib_a : fiber mapB a, from fiber.mk apr im_a,
tr fib_a

definition im_to_pred {A : Set} (pred : Setpred A) (a : A) :
  image (Subset.map (pred_to_sset pred)) a -> pred a :=
let B := pred_to_sset pred,
    mapB := Subset.map B,
    injB := Subset.inj B in
take im, 
have H : is_prop (fiber mapB a), from set_inj_implies_unique_fib mapB injB a,
have fib_a : fiber mapB a, from untrunc_of_is_trunc im,
have eq_a : (fiber.point fib_a).1 = a, from fiber.point_eq fib_a,
eq_a ▸ (fiber.point fib_a).2

/- Should be in one of the trunc files. -/
lemma prop_iff_eq : Π {A B : Prop} (imp1 : A -> B) (imp2 : B -> A), A = B 
| (Prop.mk carA structA) (Prop.mk carB structB) :=
  take imp1 imp2, 
  have car_eqv : carA ≃ carB, from 
    have rinv : forall (b : carB), imp1 (imp2 b) = b, from take b, !is_prop.elim,
    have linv : forall (a : carA), imp2 (imp1 a) = a, from take a, !is_prop.elim,
    equiv.mk imp1 (adjointify imp1 imp2 rinv linv),
  have car_eq : carA = carB, from ua car_eqv, /- Do you really need univalence here? -/
  have struct_tr : car_eq ▸ structA = structB, from !is_prop.elim,
  have struct_eq : structA =[car_eq] structB, from pathover_of_tr_eq struct_tr,
  apd011 Prop.mk car_eq struct_eq

definition map_pred_sset [reducible] {A : Set} (B : Subset A) :
  Subset.carrier (pred_to_sset (sset_to_pred B)) -> Subset.carrier B :=
let mapB := Subset.map B,
    injB := Subset.inj B in
let pred := sset_to_pred B, 
    B_pred := pred_to_sset pred in
take b_pred, 
let a := b_pred.1 in
have H : is_prop (fiber mapB a), from set_inj_implies_unique_fib mapB injB a,
let fib_a := untrunc_of_is_trunc b_pred.2 in
fiber.point fib_a 

lemma map_map_pred_sset {A : Set} (B : Subset A) : 
  forall (b_pred : Subset.carrier (pred_to_sset (sset_to_pred B))),
  Subset.map B (map_pred_sset B b_pred) = b_pred.1 :=
let mapB := Subset.map B, 
    injB := Subset.inj B in
take b_pred, 
let a := b_pred.1, im_a := b_pred.2 in
let H_prop := set_inj_implies_unique_fib mapB injB a in
calc mapB (map_pred_sset B b_pred) = 
           mapB (fiber.point (@untrunc_of_is_trunc -1 (fiber mapB a) H_prop im_a)) : 
     by rewrite ↑map_pred_sset
     ... = a : !fiber.point_eq

definition map_sset_pred {A : Set} (B : Subset A) : 
  Subset.carrier B -> Subset.carrier (pred_to_sset (sset_to_pred B)) :=
let mapB := Subset.map B in
take b, 
let a := mapB b in
dpair a (tr (fiber.mk b idp))

definition inv_pred_sset {A : Set} (B : Subset A) : 
  is_set_inverse_of (map_pred_sset B) (map_sset_pred B) :=
let f := map_pred_sset B, g := map_sset_pred B in
let mapB := Subset.map B,
    injB := Subset.inj B in
have rinv : is_set_right_inverse_of f g, from 
  take b, by esimp,
have linv : is_set_left_inverse_of f g, from 
  take b_pred, 
  have pr1_eq : (g (f b_pred)).1 = b_pred.1, from
    calc (g (f b_pred)).1 = mapB (f b_pred) : by esimp 
         ... = b_pred.1 : map_map_pred_sset B b_pred,
  sigma_prop_pr1_inj _ _ pr1_eq,
is_set_inverse_of.mk rinv linv

definition bij_pred_sset {A : Set} (B : Subset A) :
  bijection (Subset.carrier (pred_to_sset (sset_to_pred B))) (Subset.carrier B) :=
has_inverse_to_bijection (map_pred_sset B) (map_sset_pred B) (inv_pred_sset B)

definition sset_bij_pred_sset  {A : Set} (B : Subset A) :
  sset_bijection (pred_to_sset (sset_to_pred B)) B :=
let f := bij_pred_sset B in
have comp_hom : (Subset.map B) ∘ (bijection.map f) ~ Subset.map (pred_to_sset (sset_to_pred B)), from
  take b_pred, 
  calc Subset.map B (bijection.map f b_pred) = b_pred.1 : map_map_pred_sset B b_pred
       ... = Subset.map (pred_to_sset (sset_to_pred B)) b_pred : by esimp,
have comp_eq : (Subset.map B) ∘ (bijection.map f) = Subset.map (pred_to_sset (sset_to_pred B)), from
  eq_of_homotopy comp_hom,
dpair f comp_eq

definition sset_pred_linv {A : Set} (B : Subset A) : pred_to_sset (sset_to_pred B) = B := 
  bij_to_sset_eq (sset_bij_pred_sset B) 

definition Subset_equiv_Setpred (A : Set) : Subset A ≃ Setpred A :=
  have rinv : forall (pred : Setpred A), sset_to_pred (pred_to_sset pred) = pred, from 
    take pred, 
    have hom : sset_to_pred (pred_to_sset pred) ~ pred, from 
      take a, 
      calc sset_to_pred (pred_to_sset pred) a = image (Subset.map (pred_to_sset pred)) a : by esimp
           ... = pred a : prop_iff_eq (im_to_pred pred a) (pred_to_im pred a),
    eq_of_homotopy hom,
  have linv : forall (B : Subset A), pred_to_sset (sset_to_pred B) = B, from
    sset_pred_linv,
  equiv.mk sset_to_pred (adjointify sset_to_pred pred_to_sset rinv linv)  

lemma sset_pred_inj {A : Set} : forall (B C : Subset A),
  sset_to_pred B = sset_to_pred C -> B = C :=
take B C pred_eq,
have sset_pred_eq : pred_to_sset (sset_to_pred B) = pred_to_sset (sset_to_pred C), from
  ap pred_to_sset pred_eq,
calc B = pred_to_sset (sset_to_pred B) : sset_pred_linv B
     ... = pred_to_sset (sset_to_pred C) : sset_pred_eq
     ... = C : sset_pred_linv C 

/- On subsets we can introduce the standard notations of set theory and prove some 
   facts of (naive) set theory. -/
notation [parsing_only] a `∈` B := sset_to_pred B a

definition is_subset_of {A : Set} (B C : Subset A) :=
  forall a : A, a ∈ B -> a ∈ C

notation [parsing_only] B `⊆` C := is_subset_of B C

/- Two subsets are equal iff they are subsets of each other. -/
theorem sset_eq_iff_inclusion {A : Set} (B C : Subset A) :
  B = C ↔ (B ⊆ C) × (C ⊆ B) :=
have imp1 : B = C -> (B ⊆ C) × (C ⊆ B), from 
  take sset_eq, 
  have incl1 : B ⊆ C, from take a a_in_B,
    sset_eq ▸ a_in_B,
  have incl2 : C ⊆ B, from take a a_in_C,
    sset_eq⁻¹ ▸ a_in_C,
  prod.mk incl1 incl2,
have imp2 : (B ⊆ C) × (C ⊆ B) -> B = C, from 
  take incl, let incl1 := prod.pr1 incl, incl2 := prod.pr2 incl in 
  have pred_hom : sset_to_pred B ~ sset_to_pred C, from 
    take a, prop_iff_eq (incl1 a) (incl2 a),
  have pred_eq : sset_to_pred B = sset_to_pred C, from 
    eq_of_homotopy pred_hom,
  sset_pred_inj B C pred_eq, 
prod.mk imp1 imp2

/- TODO : Introduce operations of boolean algebra and prove formulas, 
          in new file [boolean_algebra] -/

end subset
