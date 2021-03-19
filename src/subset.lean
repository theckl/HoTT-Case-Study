import set_theory

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open hott.set hott.is_trunc hott.is_equiv hott.eq hott.trunc hott.sigma

namespace subset

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

/- Should be in [init.path]. -/
notation eq `▸[`:50 P:0 `]`:0 b:50 := transport P eq b 

@[hott]
structure Subset (A : Set.{u}) :=
   (carrier : Set.{u}) (map : carrier -> A)  (inj : is_set_injective map) 

@[hott]
instance (A : Set) : has_coe_to_sort (Subset A) := 
  has_coe_to_sort.mk Set (λ B, Subset.carrier B)

attribute [instance] Subset.inj 

@[hott]
instance {A : Set} (B : Subset A) : has_coe ↥B A :=
  ⟨λ b, B.map b⟩

@[hott]
def total_Subset (A : Set) : Subset A := 
  have id_is_inj : is_set_injective (id_map A), 
    from assume a1 a2 f_eq, 
    calc a1 = (id_map A) a1 : by reflexivity
         ... = (id_map A) a2 : by rwr f_eq
         ... = a2 : by reflexivity,
  Subset.mk A (id_map A) id_is_inj 

/- The empty set is a subset of every set [A], an elegant consequence of the construction 
   of subsets. -/
@[hott]   
def empty_Subset (A : Set) : Subset A := 
  have f : empty_Set -> A, by intro e; induction e,
  have is_inj_f : is_set_injective f, by intro e; induction e,
  Subset.mk empty_Set f is_inj_f

/- The image of a map betweens sets is a subset of the codomain. We show this in several steps:
   * First, we show that [total_image] from [function] is a set. This works more generally: 
     A sigma type whose dependent components are sets is a set. It can be shown for n-types 
     using the results in [hit.trunc] on truncations of sigma types. 
   * Second, we construct a map from [total_image] into the codomain and show that it is 
     injective.
   * Now we have all the ingredients to construct the image as a subset of the codomain. -/  
@[hott]
def image_is_set {A B : Set.{u}} (f : A -> B) : is_set (total_image f) :=
    have H : forall c d : total_image f, is_prop (c = d), from 
      assume c d, 
      have forall p q : c = d, p = q, from 
        assume p q, 
        have eq1 : p..1 = q..1, from 
          @is_prop.elim (c.1 = d.1) (is_trunc_eq -1 c.1 d.1) p..1 q..1,
        let I := λ (p1 : c.1 = d.1), c.2 =[p1; λ (b : B), image f b] d.2 in    
        have eq2 : p..2 =[eq1; I] q..2, from 
          have Hchpq : change_path eq1 p..2 = q..2, from 
            let p2 := tr_eq_of_pathover (change_path eq1 p..2),
                q2 := tr_eq_of_pathover q..2 in
            have Heq_pq : p2 = q2, from is_prop.elim p2 q2,
            have H_equiv : equiv (c.2 =[q..1; λ (b : B), image f b] d.2) 
                                 (q..1 ▸[λ (b : B), image f b] c.2 = d.2), 
              from pathover_equiv_tr_eq _ _ _,
            let F := (equiv.to_fun H_equiv)⁻¹ᶠ, fib := fiber f c.1 in
            have HF : is_equiv F, from is_equiv_inv (equiv.to_fun H_equiv),
            have H_trunc1 : is_prop (q..1 ▸[λ (b : B), image f b] c.2 = d.2), 
              from 
              have H_prop : is_prop (trunc -1 fib), from is_trunc_trunc -1 _ ,
              have H_set : is_set (trunc -1 fib), from is_trunc_succ _ _,
              is_trunc_eq -1 _ _,
            have H_trunc2 : is_prop (c.2 =[q..1; λ (b : B), image f b] d.2), from 
              is_trunc_is_equiv_closed -1 F H_trunc1,
            is_prop.elim (change_path eq1 p..2) q..2,
          pathover_of_change_path eq1 p..2 q..2 Hchpq,
        sigma_eq2 eq1 eq2,
      is_prop.mk this,
    is_trunc_succ_intro H

@[hott]
def image_Set {A B : Set.{u}} (f : A -> B) := 
  Set.mk (total_image f) (image_is_set f)

@[hott]
def image_embedding {A B : Set} (f : A -> B) : (image_Set f) -> B :=
  λ (bf : total_image f), bf.1

@[hott]
lemma im_emb_is_inj {A B : Set} (f : A -> B) : 
  is_set_injective (image_embedding f) :=
let im_emb := image_embedding f in
show forall (bf1 bf2 : total_image f), im_emb bf1 = im_emb bf2 -> bf1 = bf2, from
assume bf1 bf2,
match bf1, bf2 with (sigma.mk b1 f1), (sigma.mk b2 f2) :=
  assume (im_emb_eq : b1 = b2), 
  have tr_eq : im_emb_eq ▸ f1 = f2, from is_prop.elim _ _,
  have fib_eq : f1 =[im_emb_eq; λ (b : B), image f b] f2, from 
    pathover_of_tr_eq tr_eq,
  apd011 sigma.mk im_emb_eq fib_eq 
end  

@[hott]
def Image {A B : Set} (f : A -> B) : Subset B :=
  Subset.mk (image_Set f) (image_embedding f) (im_emb_is_inj f)

@[hott]
lemma ap_car_ap_sset_mk {A : Set} (carB : Set) (mapB : carB -> A) 
  {inj1 inj2 : is_set_injective mapB} : forall (inj_eq : inj1 = inj2), 
  ap Subset.carrier (ap (Subset.mk carB mapB) inj_eq) = idpath carB :=
begin 
  intro inj_eq,
  hinduction inj_eq,
  reflexivity
end   

/- The type of subsets of [A] is a set: the power set. 
   To show this we first characterize equalities of subsets : they correspond to
   bijections of the underlying sets compatible with the inclusion maps.
   The core of the construction of this equivalence is that there may be many bijections 
   between the underlying sets, but the compatibility makes the bijection unique. -/
@[hott, reducible]
def sset_bijection {A : Set} (B C : Subset A) :=
  Σ (f : bijection ↥B ↥C), (Subset.map C) ∘ (bijection.map f) = (Subset.map B) 

@[hott, reducible]
def sset_identity {A : Set} : Π (B : Subset A), sset_bijection B B 
| (Subset.mk carB mapB injB) :=
  have bij_comp : mapB ∘ (bijection.map (identity carB)) = mapB, from 
    calc mapB ∘ (bijection.map (identity carB)) = mapB ∘ (id_map carB) : 
         by rwr identity_to_id_map carB
         ... = mapB : id_map_is_right_neutral mapB,
  sigma.mk (identity carB) bij_comp 

@[hott]
lemma sset_ident_to_ident {A : Set} : Π (B : Subset A),
  (sset_identity B).1 = identity (Subset.carrier B)
| (Subset.mk carB mapB injB) :=
  by reflexivity

@[hott]
lemma bij_eq_bij_comp_eq {A : Set} {B C : Subset A} : 
  forall fc gc : sset_bijection B C, fc.1 = gc.1 -> fc = gc :=
assume fc gc bij_eq,
let P := λ (bij : bijection ↥B ↥C), C.map ∘ bij.map = B.map in
have tr_eq : bij_eq ▸[P] fc.2 = gc.2, from is_prop.elim (bij_eq ▸[P] fc.2) gc.2,
have comp_eq : fc.2 =[bij_eq;P] gc.2, from pathover_of_tr_eq tr_eq,
sigma_eq bij_eq comp_eq

@[hott]
def sset_eq_to_bij {A : Set} {B C : Subset A} : 
  B = C -> sset_bijection B C := 
begin 
intro p,
hinduction p,
exact sset_identity B
end   

@[hott, hsimp]
lemma sset_id_to_identity {A : Set} {B : Subset A} :
  sset_eq_to_bij (idpath B) = sset_identity B :=
by reflexivity

@[hott]
/- Should be in [init.path] with [A], [B], [C] types, but the elaborator can't handle it. -/
lemma tr_fun_ext {A B C : Set.{u}} (p : A = B) : 
  forall (h : B -> C) (a : A), (p⁻¹ ▸ h) a = h (p ▸ a) :=
begin 
  hinduction p,
  intros A h,
  reflexivity
end   

/- Equalities of a structure like [Subset] consisting of 3 dependent fields are difficult to handle. 
   We need some auxiliary definitions and lemmas focussing on [Subset]-structures constructed with
   [Subset.mk] - they will be used in inductive arguments. -/
@[hott, reducible]
def bij_to_sset_map_eq {A : Set} : Π {B C : Subset A} (ss_bij : sset_bijection B C),
  Subset.map B =[bij_to_set_eq ss_bij.1; λ (B : Set), B -> A] Subset.map C
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  let P := λ (B : Set), B -> A in
  assume ss_bij,
  show mapB =[bij_to_set_eq ss_bij.1; P] mapC, from
  let f := ss_bij.1, car_eq := bij_to_set_eq f in
  let tr_map_C := car_eq⁻¹ ▸[P] mapC, fm := bijection.map f in 
  have comp : mapC ∘ fm = mapB, from ss_bij.2,
  have comp_hom : tr_map_C ~ mapC ∘ fm, from assume b,
    calc tr_map_C b = mapC (car_eq ▸ b) : by exact tr_fun_ext car_eq mapC b
         ... = mapC (fm b) : by rwr <-bij_hom_tr_eq f b,
  pathover_of_eq_tr (comp⁻¹ ⬝ (eq_of_homotopy comp_hom)⁻¹)

@[hott]
def sset_comp_eq {A : Set.{u}} (car1 car2 : Set.{u}) (map1 : car1 -> A) (map2 : car2 -> A) :=
  Σ (car_eq : car1 = car2), map1 =[car_eq; λ (B : Set), B -> A] map2

/- This is a subtle point: The equality of maps induced by the equality of subsets is
   already induced by the induced equality of carrier sets. This can be shown using
   [pathover_ap] in [init.pathover]. -/
@[hott]   
def sset_mk_eq_to_comp_eq {A : Set.{u}} {car1 car2 : Set} 
  {map1 : car1 -> A} {map2 : car2 -> A}
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2] : 
  (Subset.mk car1 map1 inj1 = Subset.mk car2 map2 inj2) -> 
    (sset_comp_eq car1 car2 map1 map2) :=
assume mk_eq, let car_eq := ap Subset.carrier mk_eq in
let map_mk_eq := apd Subset.map mk_eq in
have map_car_eq : map1 =[car_eq; λ (B : Set), B -> A] map2, from 
  pathover_ap (λ (carr : Set), carr -> A) Subset.carrier map_mk_eq,
dpair car_eq map_car_eq

@[hott, reducible, hsimp]
def sset_comp_eq_to_mk_eq {A : Set} {car1 car2 : Set} :
  Π (car_eq : car1 = car2) 
  {map1 : car1 -> A} {map2 : car2 -> A} 
  (map_eq : map1 =[car_eq; λ (B : Set), B -> A] map2) 
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2],  
  Subset.mk car1 map1 inj1 = Subset.mk car2 map2 inj2 :=
begin
intro car_eq,
hinduction car_eq,
  intros map1 map2 map_eq,
  hinduction map_eq,
    intros inj1 inj2,
    exact ap (Subset.mk car1 map1) (is_prop.elim inj1 inj2)
end    

@[hott, reducible]
def sset_comp_eq_to_sset_eq {A : Set} : Π {B C : Subset A}
  (car_eq : Subset.carrier B = Subset.carrier C) 
  (map_eq : Subset.map B =[car_eq; λ (B : Set), B -> A] Subset.map C), 
  B = C 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  assume car_eq map_eq,
  @sset_comp_eq_to_mk_eq _ _ _ car_eq _ _ map_eq injB injC

@[hott, reducible]
def ap_sset_comp_to_car {A : Set} {car1 car2 : Set} :
  Π (car_eq : car1 = car2) 
  {map1 : car1 -> A} {map2 : car2 -> A} 
  (map_eq : map1 =[car_eq; λ (B : Set), B -> A] map2) 
  [inj1 : is_set_injective map1] [inj2 : is_set_injective map2],
  ap Subset.carrier (@sset_comp_eq_to_mk_eq _ _ _ car_eq _ _ map_eq inj1 inj2) = car_eq := 
begin  
intro car_eq,  
hinduction car_eq with car_id,
  intros map1 map2 map_eq,
  hinduction map_eq,
    intros inj1 inj2,
    have eq1 : @sset_comp_eq_to_mk_eq _ _ _ (idpath car1) _ _ (idpatho map1) inj1 inj2 = 
                   ap (Subset.mk car1 map1) (is_prop.elim inj1 inj2), by reflexivity,
    rwr eq1, 
    rwr (ap_car_ap_sset_mk car1 map1 (is_prop.elim inj1 inj2))               
end  

@[hott]
def idp_comp_to_sset_id {A : Set} : Π (B : Subset A), 
  sset_comp_eq_to_sset_eq (idpath (Subset.carrier B)) (idpatho (Subset.map B)) = 
  idpath B 
| (Subset.mk carB mapB injB) := 
  have inj_eq_eq : is_prop.elim injB injB = idpath injB, from is_set.elim _ _,
  calc sset_comp_eq_to_sset_eq idp idpo = 
            @sset_comp_eq_to_mk_eq _ _ _ idp _ _ idpo injB injB : by reflexivity
       ... = ap (Subset.mk carB mapB) (is_prop.elim injB injB) : 
       by  reflexivity
       ... = ap (Subset.mk carB mapB) (idpath injB) : by rwr inj_eq_eq   
       ... = idpath (Subset.mk carB mapB injB) : by hsimp 

@[hott, reducible]
def bij_to_sset_eq {A : Set}: Π {B C : Subset A}, 
  sset_bijection B C -> B = C 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) := 
  assume comp_bij, let f := comp_bij.1 in 
  let car_eq := bij_to_set_eq f,
      map_eq := bij_to_sset_map_eq comp_bij in
  @sset_comp_eq_to_mk_eq _ _ _ car_eq _ _ map_eq injB injC

@[hott]
lemma bij_to_sset_eq_unf_eq {A : Set} : Π {B C : Subset A}
  (sset_bij : sset_bijection B C), 
  bij_to_sset_eq (sset_bij) = sset_comp_eq_to_sset_eq (bij_to_set_eq sset_bij.1) (bij_to_sset_map_eq sset_bij) 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) :=
  assume sset_bij, by refl

@[hott]
lemma identity_to_sset_id {A : Set} : Π (B : Subset A),
  bij_to_sset_eq (sset_identity B) = idpath B := 
assume B,
let carB := Subset.carrier B, mapB := Subset.map B,
    injB := Subset.inj B in 
let f := (sset_identity B).1 in
let car_eq := bij_to_set_eq f in
have car_eq_idp : car_eq = idpath carB, from 
  calc car_eq = bij_to_set_eq (sset_identity B).1 : by refl
       ... = bij_to_set_eq (identity carB) : by rwr sset_ident_to_ident B
       ... = idpath carB : identity_to_idp, 
let map_eq := bij_to_sset_map_eq (sset_identity B) in
have map_eq_eqv : (mapB =[idpath carB; λ (B : Set), B -> A] mapB) ≃ (mapB = mapB), from 
  pathover_idp (λ (B : Set), B -> A) mapB mapB,
have P : is_prop (mapB = mapB), from @is_trunc_eq _ -1 is_set_map mapB mapB,
have prop_map_eq : is_prop (mapB =[idpath carB; λ (B : Set), B -> A] mapB), from 
  is_trunc_equiv_closed_rev -1 map_eq_eqv P,
have change_po : change_path car_eq_idp map_eq = idpatho mapB, from 
  @is_prop.elim _ prop_map_eq _ _,
let E := λ (e : carB = carB), mapB =[e; λ (B : Set), B -> A] mapB in   
have map_eq_idpo : map_eq =[car_eq_idp; E] idpatho mapB, from 
  pathover_of_change_path car_eq_idp map_eq (idpatho mapB) change_po,
have unf_eq : bij_to_sset_eq (sset_identity B) = 
                sset_comp_eq_to_sset_eq car_eq map_eq, from
  bij_to_sset_eq_unf_eq (sset_identity B),
calc bij_to_sset_eq (sset_identity B) = sset_comp_eq_to_sset_eq car_eq map_eq : 
     by rwr unf_eq
     ... = sset_comp_eq_to_sset_eq (idpath carB) (idpatho mapB) : 
     apd011 (λ (eq1 : carB = carB) (eq2 : mapB =[eq1; λ (B : Set), B -> A] mapB), 
               sset_comp_eq_to_sset_eq eq1 eq2) car_eq_idp map_eq_idpo
     ... = idpath B : idp_comp_to_sset_id B

@[hott]
lemma sset_bij_eq_set_bij {A : Set} (B C : Subset A) : forall e : B = C, 
  (sset_eq_to_bij e).1 = set_eq_to_bij (ap Subset.carrier e) := 
begin
  intro e,
  hinduction e,
    hsimp, rwr sset_ident_to_ident
end    

@[hott]
lemma bij_sset_eq_bij_set {A : Set} : forall (B C : Subset A)  
  (sset_bij : sset_bijection B C) (b : Subset.carrier B), 
  ap Subset.carrier (bij_to_sset_eq sset_bij) ▸ b = bij_to_set_eq sset_bij.1 ▸ b 
| (Subset.mk carB mapB injB) (Subset.mk carC mapC injC) := 
  assume sset_bij b, 
  let car_eq := bij_to_set_eq sset_bij.1,
      map_eq := bij_to_sset_map_eq sset_bij, 
      sset_comp_eq := @sset_comp_eq_to_mk_eq _ _ _ car_eq _ _ map_eq injB injC in
  have eq1 : bij_to_sset_eq sset_bij = sset_comp_eq, by refl,
  have eq2 : ap Subset.carrier sset_comp_eq = car_eq, from 
    @ap_sset_comp_to_car _ _ _ car_eq _ _ map_eq injB injC,
  begin rwr eq1, rwr eq2 end

@[hott]
def sset_eq_equiv_bij {A : Set.{u}} (B C : Subset A) : 
  B = C ≃ sset_bijection B C := 
have rinv : forall (fc : sset_bijection B C), 
              sset_eq_to_bij (@bij_to_sset_eq A B C fc) = fc, from 
  let F := @sset_eq_to_bij A B C, G := @bij_to_sset_eq A B C in
  assume fc, let f := fc.1, FGf := (F (G fc)).1 in 
  have bijmap_hom : bijection.map FGf ~ bijection.map f, from 
    assume b, 
    calc bijection.map FGf b = bijection.map (set_eq_to_bij (ap Subset.carrier (G fc))) b : 
         apd10 (ap bijection.map (sset_bij_eq_set_bij B C (G fc))) b
         ... = (ap Subset.carrier (G fc)) ▸ b : 
         hom_eq_tr_eq (ap Subset.carrier (G fc)) b
         ... = (bij_to_set_eq f) ▸ b : bij_sset_eq_bij_set B C fc b
         ... = (bijection.map f) b : by rwr <-bij_hom_tr_eq f b,
  have bij_eq : FGf = f, from
    have bijmap_eq : bijection.map FGf = bijection.map f, from
      eq_of_homotopy bijmap_hom,
    bijection_eq_from_map_eq _ _ bijmap_eq,
  bij_eq_bij_comp_eq _ _ bij_eq,
have linv : forall e : B = C, bij_to_sset_eq (sset_eq_to_bij e) = e, 
  begin 
    intro e,
    hinduction e,
      rwr sset_id_to_identity, rwr identity_to_sset_id
  end,  
equiv.mk sset_eq_to_bij (adjointify sset_eq_to_bij bij_to_sset_eq rinv linv)

@[hott]
def Powerset_is_set {A : Set.{u}} : is_set (Subset A) := 
have H_eq : forall B C : Subset A, is_prop (B = C), from 
  assume B C,
  let mapB := Subset.map B, mapC := Subset.map C in
  have bij_eq_is_prop : is_prop (sset_bijection B C), from 
    have H_bij_eq : forall (beq1 beq2 : sset_bijection B C), beq1 = beq2, 
      from assume beq1 beq2,
      let f := beq1.1, g := beq2.1 in  
      have p_map : (bijection.map f) = (bijection.map g), from 
        have i_comp_eq : mapC ∘ f = mapC ∘ g, from 
          calc mapC ∘ f = mapB : by exact beq1.2
               ... = mapC ∘ g : by exact (beq2.2)⁻¹, 
        univ_prop_of_inj mapC (Subset.inj C) (Subset.carrier B) f g i_comp_eq, 
      have p : f = g, from bijection_eq_from_map_eq f g p_map,
      let P := λ h : bijection ↥B ↥C, C.map ∘ h.map = B.map in
      have tr_eq : p ▸[P] beq1.2 = beq2.2, from 
        is_prop.elim (p ▸[P] beq1.2) beq2.2,
      have q : beq1.2 =[p;P] beq2.2, from pathover_of_tr_eq tr_eq,  
      sigma_eq p q, 
    is_prop.mk H_bij_eq, 
  let F := equiv.to_fun (sset_eq_equiv_bij B C) in  
  @is_trunc_is_equiv_closed _ _ -1 F⁻¹ᶠ (is_equiv_inv F) bij_eq_is_prop,
@is_trunc_succ_intro (Subset A) -1 H_eq 

@[hott, reducible]
def Powerset (A : Set) : Set :=
  Set.mk (Subset A) Powerset_is_set

hott_theory_cmd "local prefix `𝒫`:100 := hott.subset.Powerset"  

/- Subsets of [A : Set] can also be defined by predicates [P : A -> Prop]. Vice versa,  
   predicates can be extracted from a subset of [A]; this yields an equivalence.
   The subset defined by a predicate uses a bundled version of the [subtype] in [types.sigma].
   TODO: Introduce the standard notation {x : A | P a} for subsets given by predicates
         overwriting the notation for subtypes. -/
@[hott, reducible]
def Setpred (A : Set.{u}) := A -> (trunctype.{u} -1) /- Here should be [Prop]. -/ 

@[hott]
def Setpred_of {A : Set} (P : A -> Prop) : Setpred A :=
  P

@[hott]
def sset_to_pred {A : Set} : Π (B : Subset A), Setpred A :=
  assume B, λ (a : A), image (Subset.map B) a

@[hott]
def is_set_pred {A : Set.{u}} : Π (pred : Setpred A), is_set (Σ (a : A), ↥(pred a)) :=
  assume pred, 
  have forall (a : A), is_set (pred a), from 
    assume a, 
    have is_prop (pred a), from trunctype.struct (pred a),
    is_trunc_succ (pred a) -1, 
  is_trunc_sigma (λ a : A, ↥(pred a)) 0  

/- Should be in one of the library files on the sigma type.
   [subtype_eq] is the subtype-version in [types.sigma]. -/
@[hott]   
def sigma_prop_pr1_inj {A : Type u} {B : A -> trunctype.{u} -1} : /- Should be [Prop]. -/
  forall (b c : Σ (a : A), B a), b.1 = c.1 -> b = c :=
assume b c pr1_eq,
have pr2_tr : pr1_eq ▸[λ a : A, B a] b.2 = c.2, from is_prop.elim _ _, 
have pr2_eq : b.2 =[pr1_eq; λ a : A, B a] c.2, from pathover_of_tr_eq pr2_tr,
sigma_eq pr1_eq pr2_eq

/- We construct carrier, map and a proof of injectivity of the subset defined 
   by a predicate separately, to be able to use these components in 
   later calculations. -/
@[hott, reducible]   
def pred_to_sset_car {A : Set} (pred : Setpred A) : Set :=
  let predset := Σ (a : A), trunctype.carrier (pred a)  in
  Set.mk predset (is_set_pred pred)  

@[hott, reducible]
def pred_to_sset_map {A : Set} (pred : Setpred A) :
  pred_to_sset_car pred -> A :=
let carr := pred_to_sset_car pred in
λ (b : carr), b.1 

@[hott, reducible]
def pred_to_sset_inj {A : Set} (pred : Setpred A) :
  is_set_injective (pred_to_sset_map pred) := 
assume b1 b2 map_eq, 
sigma_prop_pr1_inj b1 b2 map_eq

@[hott, reducible]
def pred_to_sset {A : Set} (pred : Setpred A) : 
  Subset A :=
Subset.mk (pred_to_sset_car pred) (pred_to_sset_map pred) (pred_to_sset_inj pred)

@[hott]
def pred_to_im {A : Set} (pred : Setpred A) (a : A) : 
  pred a -> image (Subset.map (pred_to_sset pred)) a :=
let B := pred_to_sset pred,
    mapB := Subset.map B in
assume p, let apr := dpair a p in /- an element in [predset] -/
have im_a : mapB apr = a, by refl, /- mapped to a -/
have fib_a : fiber mapB a, from fiber.mk apr im_a,
tr fib_a

@[hott]
def im_to_pred {A : Set} (pred : Setpred A) (a : A) :
  image (Subset.map (pred_to_sset pred)) a -> pred a :=
let B := pred_to_sset pred,
    mapB := Subset.map B,
    injB := Subset.inj B in
assume im, 
have H : is_prop (fiber mapB a), from set_inj_implies_unique_fib mapB injB a,
have fib_a : fiber mapB a, from @untrunc_of_is_trunc _ _ H im,
have eq_a : fib_a.point.1 = a, from fiber.point_eq fib_a,
eq_a ▸[λ a : A, pred a] (fiber.point fib_a).2

@[hott, reducible]
def map_pred_sset {A : Set} (B : Subset A) :
  Subset.carrier (pred_to_sset (sset_to_pred B)) -> Subset.carrier B :=
let mapB := Subset.map B,
    injB := Subset.inj B in
assume b_pred, 
let a := b_pred.1 in
have H : is_prop (fiber mapB a), from set_inj_implies_unique_fib mapB injB a,
have fib_a : fiber mapB a, from @untrunc_of_is_trunc _ _ H b_pred.2,
fiber.point fib_a 

@[hott]
lemma map_map_pred_sset {A : Set} (B : Subset A) : 
  forall (b_pred : Subset.carrier (pred_to_sset (sset_to_pred B))),
  Subset.map B (map_pred_sset B b_pred) = b_pred.1 :=
let mapB := Subset.map B, 
    injB := Subset.inj B in
assume b_pred, 
let a := b_pred.1, im_a := b_pred.2 in
let H_prop := set_inj_implies_unique_fib mapB injB a in
let fib_a := @untrunc_of_is_trunc (fiber mapB a) -1 H_prop im_a in
calc mapB (map_pred_sset B b_pred) = mapB fib_a.point : by refl
     ... = a : fib_a.point_eq

@[hott]
def map_sset_pred {A : Set} (B : Subset A) : 
  Subset.carrier B -> Subset.carrier (pred_to_sset (sset_to_pred B)) :=
let mapB := Subset.map B in
assume b, 
let a := mapB b in
dpair a (tr (fiber.mk b idp))

@[hott]
def inv_pred_sset {A : Set} (B : Subset A) : 
  is_set_inverse_of (map_pred_sset B) (map_sset_pred B) :=
let f := map_pred_sset B, g := map_sset_pred B in
let mapB := Subset.map B,
    injB := Subset.inj B in
have rinv : is_set_right_inverse_of f g, from 
  assume b, by refl,
have linv : is_set_left_inverse_of f g, from 
  assume b_pred, 
  have pr1_eq : (g (f b_pred)).1 = b_pred.1, from
    calc (g (f b_pred)).1 = mapB (f b_pred) : by refl 
         ... = b_pred.1 : map_map_pred_sset B b_pred,
  sigma_prop_pr1_inj _ _ pr1_eq,
is_set_inverse_of.mk rinv linv

@[hott]
def bij_pred_sset {A : Set} (B : Subset A) :
  bijection (Subset.carrier (pred_to_sset (sset_to_pred B))) (Subset.carrier B) :=
has_inverse_to_bijection (map_pred_sset B) (map_sset_pred B) (inv_pred_sset B)

@[hott]
def sset_bij_pred_sset  {A : Set.{u}} (B : Subset A) :
  sset_bijection (pred_to_sset (sset_to_pred B)) B :=
let f := bij_pred_sset B in
have comp_hom : (Subset.map B) ∘ (bijection.map f) ~ 
                   Subset.map (pred_to_sset (sset_to_pred B)), from
  assume b_pred, 
  calc Subset.map B (bijection.map f b_pred) = b_pred.1 : 
      map_map_pred_sset B b_pred
       ... = Subset.map (pred_to_sset (sset_to_pred B)) b_pred : by refl,
have comp_eq : (Subset.map B) ∘ (bijection.map f) = Subset.map (pred_to_sset (sset_to_pred B)), from
  eq_of_homotopy comp_hom,
dpair f comp_eq

@[hott]
def sset_pred_linv {A : Set} (B : Subset A) : pred_to_sset (sset_to_pred B) = B := 
  bij_to_sset_eq (sset_bij_pred_sset B) 

@[hott]
def Subset_equiv_Setpred (A : Set) : Subset A ≃ Setpred A :=
  have rinv : forall (pred : Setpred A), sset_to_pred (pred_to_sset pred) = pred, from 
    assume pred, 
    have hom : sset_to_pred (pred_to_sset pred) ~ pred, from 
      assume a, 
      calc sset_to_pred (pred_to_sset pred) a = 
                 image (Subset.map (pred_to_sset pred)) a : by refl
           ... = pred a : prop_iff_eq (im_to_pred pred a) (pred_to_im pred a),
    eq_of_homotopy hom,
  have linv : forall (B : Subset A), pred_to_sset (sset_to_pred B) = B, from
    sset_pred_linv,
  equiv.mk sset_to_pred (adjointify sset_to_pred pred_to_sset rinv linv)  

@[hott]
def sset_pred_inj {A : Set} : forall (B C : Subset A),
  sset_to_pred B = sset_to_pred C -> B = C :=
assume B C pred_eq,
have sset_pred_eq : @pred_to_sset A (@sset_to_pred A B) = pred_to_sset (sset_to_pred C), from
  ap pred_to_sset pred_eq,
calc B = pred_to_sset (sset_to_pred B) : (sset_pred_linv B)⁻¹ 
     ... = pred_to_sset (sset_to_pred C) : sset_pred_eq
     ... = C : sset_pred_linv C 

/- On subsets we can introduce the standard notations of set theory and prove some 
   facts of (naive) set theory. -/
variables {A : Set.{u}}

@[hott]
protected def elem (a : A) (S : Subset A) :=
sset_to_pred S a 

hott_theory_cmd "local infix  `∈`:70 := hott.subset.elem"

@[hott, instance]
def is_prop_elem (a : A) (S : Subset A) : is_prop (a ∈ S) :=
  (a ∈ S).struct  

notation `{ ` binder ` ∈ ` B ` | ` P:scoped  ` }` := @pred_to_sset B P 

#check hott.is_equiv.right_inv

@[hott, reducible, hsimp]
def pred_elem {A : Set} {P : Setpred A} (a : A) : a ∈ { a ∈ A | P a } -> P a :=
  assume elem_a_P, by rwr <- (is_equiv.right_inv (Subset_equiv_Setpred A).to_is_equiv) a

@[hott, reducible]
def elem_pred {A : Set} {P : Setpred A} (a : A) (pred_a : P a) :
  { a ∈ A | P a }.carrier :=    
⟨a, pred_a⟩

@[hott]
def elem_pred_eq {A : Set} {P : Setpred A} (a : A) (pred_a : P a) :
  ({ a ∈ A | P a }).map (elem_pred a pred_a) = a :=
by hsimp  

@[hott]
def is_subset_of (B C : Subset A) :=
  forall a : A, a ∈ B -> a ∈ C

notation [parsing_only] B `⊆` C := is_subset_of B C

@[hott, instance]
def is_prop_subset (B C : Subset A) : is_prop (B ⊆ C) :=
  have Pss : ∀ a : A, is_prop (a ∈ B -> a ∈ C), from 
    assume a, is_prop_map ((a ∈ C).struct),
  is_prop_dprod Pss

@[hott]   
inductive construct_elem (P : A → trunctype.{u} -1) /- Should be [Prop]. -/
| intro (w : A) (h : P w) : construct_elem

attribute [intro] construct_elem.intro

def exists_elem {A : Set} (P : A → Prop) : Prop :=
  ∥ construct_elem P ∥ 

notation `∃` binder `∈` B `,` P:scoped := @exists_elem B P 

/- Two subsets are equal iff they are subsets of each other. -/
@[hott]
def sset_eq_iff_inclusion {A : Set} (B C : Subset A) :
  B = C ↔ (B ⊆ C) × (C ⊆ B) :=
have imp1 : B = C -> (B ⊆ C) × (C ⊆ B), from 
  assume sset_eq, 
  have incl1 : B ⊆ C, from assume a a_in_B,
    sset_eq ▸ a_in_B,
  have incl2 : C ⊆ B, from assume a a_in_C,
    sset_eq⁻¹ ▸ a_in_C,
  prod.mk incl1 incl2,
have imp2 : (B ⊆ C) × (C ⊆ B) -> B = C, from 
  assume incl, let incl1 := prod.fst incl, incl2 := prod.snd incl in 
  have pred_hom : sset_to_pred B ~ sset_to_pred C, from 
    assume a, prop_iff_eq (incl1 a) (incl2 a),
  have pred_eq : sset_to_pred B = sset_to_pred C, from 
    eq_of_homotopy pred_hom,
  sset_pred_inj B C pred_eq, 
prod.mk imp1 imp2

/- TODO : Introduce operations of boolean algebra on subsets and prove formulas, 
          in new file [setalgebra] -/

end subset

end hott