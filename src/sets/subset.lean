import sets.basic 

universes u v w
hott_theory

namespace hott
open hott.set hott.is_trunc hott.is_equiv hott.eq hott.trunc hott.sigma 

namespace subset

set_option pp.universes true

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

@[hott]
structure Subset (A : Set) :=
   (carrier : Set) (map : carrier -> A)  (inj : is_set_injective map) 

@[hott]
instance (A : Set) : has_coe_to_sort (Subset A) := 
  has_coe_to_sort.mk Set (λ B, Subset.carrier B)

attribute [instance] Subset.inj 

@[hott]
instance {A : Set} (B : Subset A) : has_coe ↥B ↥A :=
  ⟨λ b, B.map b⟩

@[hott]
def Subset_ulift {A : Set.{u}} : (Subset.{u v} A) -> (Subset.{u (max v w)} A) :=
  assume B,
  let B_ulift := trunctype_ulift.{v (max v w)} B.carrier,
      car_down : B_ulift -> B.carrier := λ b, b.down,
      id_ulift := B.map ∘ car_down in
  have car_down_is_inj : is_set_injective car_down, from 
    assume b₁ b₂ d_eq, 
    have bd_eq : b₁.down = b₂.down, from d_eq,
    calc b₁ = ulift.up b₁.down : (up_down_eq b₁)⁻¹
         ... = ulift.up b₂.down : by rwr bd_eq
         ... = b₂ : up_down_eq b₂, 
  have id_ulift_is_inj : is_set_injective id_ulift, from 
    @comp_inj_inj _ _ _ car_down B.map car_down_is_inj B.inj,    
  Subset.mk B_ulift id_ulift id_ulift_is_inj

@[hott]
def total_Subset (A : Set.{u}) : Subset.{u (max u w)} A := 
  have id_is_inj : is_set_injective (id_map A), 
    from assume a1 a2 f_eq, 
    calc a1 = (id_map A) a1 : by reflexivity
         ... = (id_map A) a2 : by rwr f_eq
         ... = a2 : by reflexivity,
  Subset_ulift.{u u w} (Subset.mk A (id_map A) id_is_inj) 

/- The empty set is a subset of every set [A], an elegant consequence of the construction 
   of subsets. -/
@[hott]   
def empty_Subset (A : Set) : Subset A := 
  have f : empty_Set -> A, by intro e; induction e,
  have is_inj_f : is_set_injective f, by intro e; induction e,
  Subset.mk empty_Set f is_inj_f

/- The image of a map betweens sets applied on a subset of the domain is a subset of the 
   codomain. We show this in several steps:
   * First, we generalize [image] from [function] to the image of a subset and show that it is 
     a set. This works more generally: A sigma type whose dependent components are sets is a 
     set. It can be shown for n-types using the results in [hit.trunc] on truncations of sigma types. 
   * Second, we construct a map from [ss_image] into the codomain and show that it is 
     injective.
   * Now we have all the ingredients to construct the image of a subset as a subset of the 
     codomain. -/  
@[hott]
def ss_image {A B : Set} (f : A -> B) (C : Subset A) : Type _ := 
  Σ (b : B), image (f ∘ C.map) b

@[hott, instance]
def ss_image_is_set {A B : Set} (f : A -> B) (C : Subset A) : is_set (ss_image f C) :=
begin 
  fapply is_set.mk, intros c₁ c₂ p q, 
  fapply sigma_eq2, 
  { fapply is_prop.elim },
  { fapply pathover_of_change_path, fapply is_prop.elim }
end   

@[hott]
def ss_image_Set {A B : Set} (f : A -> B) (C : Subset A) := 
  Set.mk (ss_image f C) (ss_image_is_set f C)

@[hott]
def ss_image_embedding {A B : Set} (f : A -> B) (C : Subset A) : (ss_image_Set f C) -> B :=
  λ (bf : ss_image f C), bf.1

@[hott]
def ss_im_emb_is_inj {A B : Set} (f : A -> B) (C : Subset A) : 
  is_set_injective (ss_image_embedding f C) :=
begin
  intros bf₁ bf₂ im_emb_eq, hinduction bf₁ with b₁ im₁, hinduction bf₂ with b₂ im₂,
  fapply sigma_eq,
  { assumption },
  { apply pathover_of_tr_eq, apply is_prop.elim }
end    

@[hott]
def ss_Image {A B : Set} (f : A -> B) (C : Subset A) : Subset B :=
  Subset.mk (ss_image_Set f C) (ss_image_embedding f C) (ss_im_emb_is_inj f C)

@[hott]
def Image {A B : Set} (f : A -> B) : Subset B :=
  ss_Image f (total_Subset A)

/- A small lemma needed later on. -/
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
def sset_ident_to_ident {A : Set} : Π (B : Subset A),
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
lemma tr_fun_ext {A B : Set} {C : Set} (p : A = B) : 
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
def sset_comp_eq {A : Set} (car1 car2 : Set) (map1 : car1 -> A) (map2 : car2 -> A) :=
  Σ (car_eq : car1 = car2), map1 =[car_eq; λ (B : Set), B -> A] map2

/- This is a subtle point: The equality of maps induced by the equality of subsets is
   already induced by the induced equality of carrier sets. This can be shown using
   [pathover_ap] in [init.pathover]. -/
@[hott]   
def sset_mk_eq_to_comp_eq {A : Set} {car1 car2 : Set} 
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
def bij_to_sset_eq {A : Set} : Π {B C : Subset A}, 
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
def sset_bij_eq_set_bij {A : Set} (B C : Subset A) : forall e : B = C, 
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
    @ap_sset_comp_to_car A _ _ car_eq _ _ map_eq injB injC,
  begin rwr eq1, rwr eq2 end

@[hott]
def sset_eq_equiv_bij {A : Set} (B C : Subset A) : 
  B = C ≃ sset_bijection B C := 
have rinv : forall (fc : sset_bijection B C), 
              sset_eq_to_bij (bij_to_sset_eq fc) = fc, from 
  let F := @sset_eq_to_bij A B C, G := @bij_to_sset_eq A B C in
  assume fc, let f := fc.1, FGf := (F (G fc)).1 in 
  have bijmap_hom : bijection.map FGf ~ bijection.map f, from 
    assume b, 
    calc bijection.map FGf b = bijection.map (set_eq_to_bij (ap Subset.carrier (G fc))) b : 
         apd10 (ap bijection.map (sset_bij_eq_set_bij B C (G fc))) b
         ... = (ap Subset.carrier (G fc)) ▸ b : 
         hom_eq_tr_eq (ap Subset.carrier (G fc)) b
         ... = (bij_to_set_eq f) ▸ b : bij_sset_eq_bij_set _ _ fc b
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
def ss_eq_is_prop {A : Set} (B C : Subset A) : is_prop (B = C) :=
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
  @is_trunc_is_equiv_closed _ _ -1 F⁻¹ᶠ (is_equiv_inv F) bij_eq_is_prop 

@[hott, instance]
def Powerset_is_set {A : Set.{u}} : is_set (Subset A) := 
have H_eq : forall B C : Subset A, is_prop (B = C), from 
  assume B C, ss_eq_is_prop.{u v v} B C,
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
def Setpred (A : Set) := A -> trunctype -1

@[hott]
def Setpred_of {A : Set} (P : A -> Prop) : Setpred A :=
  P

@[hott]
def sset_to_pred {A : Set} : Π (B : Subset A), Setpred A :=
  assume B, λ (a : A), image (Subset.map B) a

@[hott]
def total_pred {A : Set.{u}} (a : A) : sset_to_pred (total_Subset.{u w} A) a = True :=
  inhabited_Prop_eq _ _ (tr ⟨ulift.up a, idp⟩) true.intro

@[hott]
def empty_pred {A : Set} (a : A) : sset_to_pred (empty_Subset A) a = False :=
  have ne : ¬(sset_to_pred (empty_Subset A) a), from 
    begin intro p, hinduction p with e, hinduction e.1 end,
  uninhabited_Prop_eq _ _ ne False_uninhabited  

@[hott]
def is_set_pred {A : Set} : Π (pred : Setpred A), is_set (Σ (a : A), ↥(pred a)) :=
  assume pred, 
  have forall (a : A), is_set (pred a), from 
    assume a, 
    have is_prop (pred a), from trunctype.struct (pred a),
    is_trunc_succ (pred a) -1, 
  is_trunc_sigma (λ a : A, ↥(pred a)) 0  

/- Should be in one of the library files on the sigma type.
   [subtype_eq] is the subtype-version in [types.sigma]. -/
@[hott]   
def sigma_prop_pr1_inj {A : Type _} {B : A -> Prop} :
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
  let predset := Σ (a : A), pred a  in
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
def sset_bij_pred_sset  {A : Set} (B : Subset A) :
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
def sset_pred_rinv {A : Set} (pred : Setpred A) : 
  sset_to_pred (pred_to_sset pred) = pred :=
have hom : sset_to_pred (pred_to_sset pred) ~ pred, from 
  assume a, 
  calc sset_to_pred (pred_to_sset pred) a = 
                 image (Subset.map (pred_to_sset pred)) a : by refl
       ... = pred a : prop_iff_eq (im_to_pred pred a) (pred_to_im pred a),
    eq_of_homotopy hom  

@[hott]
def Subset_equiv_Setpred (A : Set) : Subset A ≃ Setpred A :=
  have rinv : forall (pred : Setpred A), sset_to_pred (pred_to_sset pred) = pred, from 
    assume pred, sset_pred_rinv pred,
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
@[hott]
protected def elem {A : Set} (a : A) (S : Subset A) :=
sset_to_pred S a

@[hott]
protected def not_elem {A : Set} (a : A) (S : Subset A) :=
  Not (sset_to_pred S a)

hott_theory_cmd "local infix  `∈`:70 := hott.subset.elem"
hott_theory_cmd "local infix  `∉`:70 := hott.subset.not_elem"  

@[hott]
def all_elem {A : Set} (a : A) : a ∈ total_Subset A :=
begin 
  change ↥(sset_to_pred (total_Subset A) a), 
  rwr total_pred a, exact true.intro
end

@[hott]
def empty_not_elem {A : Set} (a : A) : a ∉ empty_Subset A :=
  begin intro ne, rwr empty_pred a at ne, apply False_uninhabited, assumption end

@[hott, instance]
def is_prop_elem {A : Set} (a : A) (S : Subset A) : is_prop (a ∈ S) :=
  (a ∈ S).struct  

notation `{ ` binder ` ∈ ` B ` | ` P:scoped  ` }` := @pred_to_sset B P 

@[hott, reducible]
def pred_elem {A : Set} {P : Setpred A} (a : A) : a ∈ { a ∈ A | P a } <-> P a :=
  have imp₁ : a ∈ { a ∈ A | P a } -> P a, from
    assume elem_a_P, by rwr <- sset_pred_rinv P; assumption,
  have imp₂ : P a -> a ∈ { a ∈ A | P a }, from
    assume pred_a, 
    begin
      change ↥(sset_to_pred (pred_to_sset P) a),
      rwr sset_pred_rinv; assumption,
    end,  
  ⟨imp₁, imp₂⟩ 

@[hott, reducible]
def elem_pred {A : Set} {P : Setpred A} (a : A) (pred_a : P a) :
  {a ∈ A | P a}.carrier :=    
⟨a, pred_a⟩

@[hott]
def elem_pred_eta {A : Set} {P : Setpred A} (a : A) (pred_a : P a) :
  ({ a ∈ A | P a }).map (elem_pred a pred_a) = a :=
by hsimp 

@[hott]
def sset_elem_pred {A : Set} {P : Setpred A} (b : (↥(pred_to_sset P) : Set)) : 
  P ↑b := b.2

@[hott]
def obj_elem {A : Set} {B : Subset A} (b : B.carrier) : ↑b ∈ B :=
  have p : B.map b = ↑b, from rfl, tr ⟨b, p⟩

@[hott]
def elem_obj {A : Set} {B : Subset A} (a : A) (H : a ∈ B) : ↥B :=
  have Hp : is_prop (fiber B.map a), from set_inj_implies_unique_fib _ B.inj a,
  (@untrunc_of_is_trunc _ -1 Hp H).1   

@[hott]
def elem_obj_eq {A : Set} {B : Subset A} (a : A) (H : a ∈ B) : B.map (elem_obj a H) = a :=
  have Hp : is_prop (fiber B.map a), from set_inj_implies_unique_fib _ B.inj a,
  (@untrunc_of_is_trunc _ -1 Hp H).2

@[hott]
def is_subset_of {A : Set} (B C : Subset A) :=
  forall a : A, a ∈ B -> a ∈ C

@[hott, instance]
def is_prop_subset {A : Set} (B C : Subset A) : is_prop (is_subset_of B C) :=
  have Pss : ∀ a : A, is_prop (a ∈ B -> a ∈ C), from 
    assume a, is_prop_map ((a ∈ C).struct),
  is_prop_dprod Pss

@[hott]
def is_Subset_of {A : Set} (B C : Subset A) : trunctype -1 :=
  Prop.mk (is_subset_of B C) (is_prop_subset B C)

hott_theory_cmd "local infix `⊆`:50 := hott.subset.is_Subset_of"

@[hott]
def sset_trans {A : Set} {B C D : Subset A} : B ⊆ C -> C ⊆ D -> B ⊆ D :=
begin intros BC CD b bB, exact CD b (BC b bB) end  

@[hott]   
inductive construct_elem {A : Set} (P : A → trunctype -1) 
| intro (w : A) (h : P w) : construct_elem

attribute [intro] construct_elem.intro

def exists_elem {A : Set} (P : A → Prop) : Prop :=
  ∥ construct_elem P ∥ 

notation `∃` binder `∈` B `,` P:scoped := @exists_elem B P 

/- A criterion for not being a subset -/
@[hott]
def not_ss_elem {A : Set} (B₁ B₂ : Subset A) : 
  Not (B₁ ⊆ B₂) <-> ∃ a ∈ A, a ∈ B₁ and Not (a ∈ B₂) :=
begin 
  apply pair,
  { intro not_ss, 
    have ex_not_imp : ↥∥Σ a : A, Not (to_Prop (a ∈ B₁ -> a ∈ B₂))∥, from 
      (not_all _).1 not_ss, 
    hinduction ex_not_imp with eni, 
    apply tr, fapply construct_elem.intro, 
    { exact eni.1 },
    { exact (neg_imp _ _).1 eni.2 } },
  { intros ex Bss, hinduction ex with cons, hinduction cons with a' Pa, 
    exact (neg_imp _ _).2 Pa (Bss a') }
end    

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

/- Some lemmas to exploit the image of a subset under a map. -/
@[hott]
def ss_image_preimage {A B : Set} (f : A -> B) (C : Subset A) : 
  ∀ b : B, b ∈ ss_Image f C -> image (f ∘ C.map) b :=
begin intros b el, hinduction el with fa, rwr <- fa.2, exact fa.1.2 end 

@[hott]
def ss_image_el {A B : Set} (f : A -> B) (C : Subset A) : 
  ∀ (a : A), a ∈ C -> f a ∈ ss_Image f C :=
begin 
  intros a ela,
  apply tr, fapply fiber.mk, 
    { fapply dpair, 
      { exact f a },
      { apply tr, fapply fiber.mk, 
        { exact elem_obj a ela },
        { change f (C.map (elem_obj a ela)) = f a, 
          rwr elem_obj_eq a ela } } },
    { exact idp } 
  end

@[hott]
def ss_im_preim_el {A B : Set} (f : A -> B) (C : Subset A) (b : B) :
  b ∈ ss_Image f C -> ∥Σ a : A, (a ∈ C) × (f a = b)∥ :=
begin 
  intro elb,
  have imb : ↥(image (f ∘ C.map) b), from ss_image_preimage f C b elb,
  hinduction imb with fibb,
  exact tr ⟨C.map fibb.1, ⟨obj_elem fibb.1, fibb.2⟩⟩
end  

@[hott]
def ss_im_comp {A B C : Set} (f : A -> B) (g : B -> C) (D : Subset A) :
  ss_Image g (ss_Image f D) = ss_Image (g ∘ f) D :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros c elc, 
    let imc := ss_image_preimage g (ss_Image f D) c elc,
    hinduction imc with fibc,
    let b := (ss_Image f D).map fibc.1,
    have elb : ↥(b ∈ ss_Image f D), from tr ⟨fibc.1, idp⟩,
    let ima := ss_im_preim_el f D b elb,
    hinduction ima with H, let a := H.1,
    have p : c = g (f a), by rwr H.2.2; rwr <- fibc.2, 
    rwr p, exact ss_image_el (g ∘ f) D a H.2.1 },
  { intros c elc, 
    let ima := ss_im_preim_el (g ∘ f) D c elc,
    hinduction ima with H, let a := H.1, let b := f a,
    rwr <- H.2.2, change ↥((g b)∈ss_Image g (ss_Image f D)),
    exact ss_image_el g (ss_Image f D) b (ss_image_el f D a H.2.1) }
end    

end subset

end hott