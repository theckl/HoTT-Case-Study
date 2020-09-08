import hott.init set_theory

universes u v w
hott_theory

namespace hott
open hott.set is_trunc

namespace subset

/- We define subsets of sets [A] as a set [B] together with an injective map [i: B -> A],
   implemented as a bundled structure.  -/

@[hott]
structure Subset (A : Set) :=
   (carrier : Set) (map : carrier -> A) (inj : is_set_injective map)

@[hott]
instance sset_to_set (A : Set) :
  has_coe_to_sort (Subset A) := 
has_coe_to_sort.mk Set (λ B, B.carrier)

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
definition image_is_set {A B : Set} (f : A -> B) : is_set (total_image f) :=
    have H : forall c d : total_image f, is_prop (c = d), from 
      assume c d, 
      have forall p q : c = d, p = q, from 
        assume p q, 
        have eq1 : p..1 = q..1, from 
          @is_prop.elim (c.1 = d.1) (is_trunc_eq -1 c.1 d.1) p..1 q..1, 
        let B := λ (p1 : c.1 = d.1), c.2 =[p1] d.2 in    
        have eq2 : p..2 =[eq1; B] q..2, from 
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

#check coe_sort

end subset

end hott