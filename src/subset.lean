import hott.init set_theory

universes u v w
hott_theory

namespace hott
open hott.set hott.is_trunc hott.is_equiv eq hott.trunc hott.sigma

namespace subset

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

@[hott]
structure Subset (A : Set) :=
   (carrier : Set) (map : carrier -> A) (inj : is_set_injective map)

@[hott]
instance sset_to_set (A : Set) : has_coe_to_sort (Subset A) := 
  has_coe_to_sort.mk Set (λ B, Subset.carrier B)

attribute [instance] Subset.inj 

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
  have f : empty_Set -> A, from assume e, empty.elim e,
  have is_inj_f : is_set_injective f, from assume e, empty.elim e,
  Subset.mk empty_Set f is_inj_f

/- The image of a map betweens sets is a subset of the codomain. We show this in several steps:
   * First, we show that [total_image] from [function] is a set. This works more generally: 
     A sigma type whose dependent components are sets is a set. It can be shown for n-types 
     using the results in [hit.trunc] on truncations of sigma types. 
   * Second, we construct a map from [total_image] into the codomain and show that it is 
     injective.
   * Now we have all the ingredients to construct the image as a subset of the codomain. -/  
@[hott]
def image_is_set {A B : Set} (f : A -> B) : is_set (total_image f) :=
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
                                 (transport (λ (b : B), image f b) q..1 c.2 = d.2), 
              from pathover_equiv_tr_eq _ _ _,
            let F := (equiv.to_fun H_equiv)⁻¹ᶠ, fib := fiber f c.1 in
            have HF : is_equiv F, from is_equiv_inv (equiv.to_fun H_equiv),
            have H_trunc1 : is_prop (transport (λ (b : B), image f b) q..1 c.2 = d.2), 
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
def image_Set {A B : Set} (f : A -> B) := 
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
let car_sset := λ (inj1 inj2 : is_set_injective mapB) (inj_eq : inj1 = inj2),
                  ap Subset.carrier (ap (Subset.mk carB mapB) inj_eq) = idpath carB in
have H : Π (inj1 : is_set_injective mapB), car_sset inj1 inj1 idp, from
  assume inj1, 
  show ap Subset.carrier (ap (Subset.mk carB mapB) (idpath inj1)) = idpath carB,
    by reflexivity,
assume inj_eq, rec_unbased H inj_eq

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

end subset

end hott