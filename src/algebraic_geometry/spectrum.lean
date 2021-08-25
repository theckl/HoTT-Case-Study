import rings.modules topology.basic

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.set hott.subset hott.trunc

namespace algebraic_geometry

set_option pp.universes false

/- The prime spectrum of a ring `R` is the set of prime ideals of `R`. -/
@[hott]
def prime_spectrum (R : CommRing) := PrimeIdeal_Set R

/- We introduce the zero locus and the vanishing ideal and show some relations. -/
@[hott, reducible]
def zero_locus_pred (R : CommRing) : 
  Ideal_Set R -> Subset (pred_Set (prime_spectrum R)) :=
λ I P, prop_resize (I.1 ⊆ P.1)

@[hott, reducible]
def zero_locus {R : CommRing} : Ideal_Set R -> Subset (pred_Set (prime_spectrum R)) :=
  λ I, (zero_locus_pred R I)

@[hott]
def is_Zariski_closed {R : CommRing} : 
  Subset (pred_Set (prime_spectrum R)) -> trunctype.{0} -1 :=
λ Z, prop_resize (image (zero_locus_pred R) Z)

@[hott]
def zero_pred_zero {R : CommRing} (I : Ideal R) (U : Subset (pred_Set (prime_spectrum R))) :
  zero_locus_pred R I = U -> zero_locus I = U :=
begin  
  intro H, 
  apply (sset_eq_iff_inclusion (zero_locus I) U).2, fapply pair,
  { intros P Pz, change ↥(U P), rwr <- (homotopy_of_eq H P), 
    exact elem_to_pred P Pz },
  { intros P PU, apply pred_to_elem P, change ↥(zero_locus_pred R I P), 
    rwr H, assumption }
end  

@[hott]
def inc_prime_el_zero {R : CommRing} (I : Ideal R) (P : (pred_Set (prime_spectrum R))) :
  I.carrier ⊆ P.1 -> P ∈ zero_locus I :=
begin 
  intro ss_IP, 
  change ↥((zero_locus_pred R I) P), 
  apply pred_to_elem P, exact prop_to_prop_resize ss_IP
end    

@[hott]
def el_zero_inc_prime {R : CommRing} (I : Ideal R) (P : (pred_Set (prime_spectrum R))) :
  P ∈ zero_locus I -> I.carrier ⊆ P.1 :=
begin 
  intro elP, 
  exact prop_resize_to_prop (elem_to_pred P elP)
end

@[hott]
def ideal_inc_to_zero_inc {R : CommRing} (I J : Ideal R) :
  I.carrier ⊆ J.carrier -> zero_locus J ⊆ zero_locus I :=
begin  
  intros IJ P, 
  change (zero_locus_pred R J) P -> (zero_locus_pred R I) P,
  intro PJ, apply pred_to_elem P,
  exact prop_to_prop_resize (subset_trans _ _ _ IJ (prop_resize_to_prop (elem_to_pred P PJ)))
end    

@[hott]
def zero_ideal_isum {R : CommRing} {I : Set} (f : I -> Ideal_Set R) : 
  ∀ P : pred_Set (prime_spectrum R), P ∈ (zero_locus (ideal_isum I f)) <-> 
                                                   P ∈ (⋂ᵢ ((@zero_locus R) ∘ f)) :=
begin
  intro P, fapply pair, 
  { intro elP, let incP := el_zero_inc_prime (ideal_isum I f) P elP, 
    apply (pred_elem P).2, apply prop_to_prop_resize, intro i, apply (pred_elem P).2, 
    exact prop_to_prop_resize (subset_trans _ _ _ (ideal_inc_isum f i) incP) },
  { intros elP, apply (pred_elem P).2, 
    let ssP := (pred_elem P).1 elP, apply prop_to_prop_resize, apply ideal_isum_inc, 
    intro i, apply el_zero_inc_prime, 
    exact (prop_resize_to_prop ssP) i }   
end

@[hott]
def vanish_ideal (R : CommRing) : Subset (pred_Set (prime_spectrum R)) -> Ideal_Set R :=
  assume U, submodule_sInter (@ss_Image (pred_Set (prime_spectrum R)) (Ideal_Set R) 
                                                      (pred_Set_map (PrimeIdeal_Set R)) U)

@[hott]
def prime_vanish_inc {R : CommRing} {U : Subset (pred_Set (prime_spectrum R))} 
  (P : pred_Set (prime_spectrum R)) : P ∈ U -> (vanish_ideal R U).carrier ⊆ P.1.carrier :=
assume elPU, submod_sInter_inc _ P.1 (ss_image_el _ _ P elPU)   

def zero_pred_vanish {R : CommRing} (I : Ideal_Set R) (U : Subset (pred_Set (prime_spectrum R))) :
  (zero_locus_pred R I = U) -> (I.carrier ⊆ (vanish_ideal R U).carrier) :=
begin  
  intro pred_eq, apply sset_sInter, intros C elC,
  let elC' := (@ss_im_comp (pred_Set (PrimeIdeal_Set R)) (Ideal_Set R) 
    (𝒫 (ring_as_module R).carrier) (pred_Set_map (PrimeIdeal_Set R)) 
                                                    Submodule.to_Subset U C).1 elC,
  let imP := ss_im_preim_el _ U C elC',
  hinduction imP with H, let P := H.1, rwr <- H.2.2, 
  change ↥(I.carrier⊆P.1.carrier), 
  have elP : ↥(P ∈ zero_locus I), by rwr zero_pred_zero I U pred_eq; exact H.2.1,
  exact prop_resize_to_prop ((pred_elem P).1 elP)   
end    

@[hott]
def Zcl_to_ZV_eq {R : CommRing} (U : Subset (pred_Set (prime_spectrum R))) : 
  is_Zariski_closed U -> (zero_locus (vanish_ideal R U) = U) :=
begin
  intro ZclU, hinduction (prop_resize_to_prop ZclU) with eqU fibU, let I := fibU.1,
  apply (sset_eq_iff_inclusion (zero_locus (vanish_ideal R U)) U).2, fapply pair, 
  { rwr <- zero_pred_zero I U fibU.2, 
    apply ideal_inc_to_zero_inc, rwr zero_pred_zero I U fibU.2,
    exact zero_pred_vanish I U fibU.2 },
  { intros P elP, apply (pred_elem P).2, 
    exact prop_to_prop_resize (prime_vanish_inc P elP) }
end     

@[hott]
def ZV_eq_to_Zcl {R : CommRing} (U : Subset (pred_Set (prime_spectrum R))) : 
  (zero_locus (vanish_ideal R U) = U) -> is_Zariski_closed U :=
begin  
  intro ZVU, apply prop_to_prop_resize, apply tr, fapply fiber.mk, 
  { exact vanish_ideal R U },
  { apply eq_of_homotopy, intro P, apply prop_iff_eq _ _, 
    { intro l_ss_VP, change ↥(P ∈ U), rwr <- ZVU, 
      apply pred_to_elem P l_ss_VP },
    { intro elP, have elP' : ↥(P ∈ U), from elP, rwr <- ZVU at elP',
      exact elem_to_pred P elP' } }
end    

/- Now we show the properties needed to construct the Zariski topology from Zariski-closed 
   sets. -/
@[hott]
def empty_Zariski_closed (R : CommRing) : 
  is_Zariski_closed (empty_Subset (pred_Set (prime_spectrum R))) :=
begin 
  apply prop_to_prop_resize, apply tr, 
  have all_empty : zero_locus_pred R (R•1) = 
                   (empty_Subset (pred_Set (prime_spectrum R))), from 
    begin 
      apply eq_of_homotopy, intro P, 
      change prop_resize ((R•1).carrier ⊆ P.1) =
                          (empty_Subset (pred_Set (prime_spectrum R)) P),                    
      rwr Not_eq_False (empty_not_elem P), rwr <- pr_rinv False, 
      apply ap prop_resize, rwr False_ulift_eq, 
      exact Not_eq_False (@proper_prime_ideal R P.1 (prime_is_prime P)) 
    end,
  exact ⟨R•1, all_empty⟩
end 

@[hott]
def union_Zariski_closed (R : CommRing) : Π U V : Subset (pred_Set (prime_spectrum R)), 
  is_Zariski_closed U -> is_Zariski_closed V -> is_Zariski_closed (U ∪ V) :=
begin  
  intros U V clU clV, hinduction (prop_resize_to_prop clU) with eqU IU, 
  hinduction (prop_resize_to_prop clV) with eqV IV, apply prop_to_prop_resize, apply tr,
  have union_inter : zero_locus_pred R (ideal.inter IU.1 IV.1) = (U ∪ V), from
    begin
      apply eq_of_homotopy, intro P, 
      change prop_resize ((IU.1.1 ∩ IV.1.1) ⊆ P.1) = P∈(U ∪ V),
      apply prop_iff_eq,
      { intro inter_inc, apply (pred_elem P).2, rwr <- IU.2, rwr <- IV.2,
        change ↥(prop_resize (IU.1.1 ⊆ P.1) or prop_resize (IV.1.1 ⊆ P.1)),
        rwr <- prop_resize_or, apply prop_to_prop_resize, 
        apply (inter_prime _ IU.1 IV.1 (prime_is_prime P)).1,
        exact prop_resize_to_prop inter_inc },
      { intro el_un, apply prop_to_prop_resize, 
        apply (inter_prime _ IU.1 IV.1 (prime_is_prime P)).2,
        apply prop_resize_to_prop, rwr prop_resize_or, 
        change ↥(P∈zero_locus_pred R IU.point or P∈zero_locus_pred R IV.point),
        rwr IU.2, rwr IV.2, exact (pred_elem P).1 el_un }
    end,
  exact ⟨ideal.inter IU.1 IV.1, union_inter⟩
end    

@[hott]
def inter_Zariski_closed (R : CommRing) : 
  ∀ (I : Set) (f : I -> 𝒫 (pred_Set (prime_spectrum R))), 
          (∀ i : I, is_Zariski_closed (f i)) -> is_Zariski_closed (⋂ᵢ f) :=
begin 
  intros I f clfI,  
  apply prop_to_prop_resize, apply tr, fapply fiber.mk,  
  { exact ideal_isum I ((vanish_ideal R) ∘ f) },
  { apply eq_of_homotopy, intro P, change _ = P ∈ (⋂ᵢ f),
    have imp1 : P ∈ (⋂ᵢ f) -> to_Prop (∀ i, P ∈ f i), from 
      begin intro elP, exact prop_resize_to_prop (elem_to_pred P elP) end,
    have imp2 : to_Prop (∀ i, P ∈ f i) -> P ∈ (⋂ᵢ f), from 
      begin intro elPi, exact pred_to_elem P (prop_to_prop_resize elPi) end,
    have imp3 : to_Prop (∀ i, P ∈ f i) -> 
                  to_Prop (∀ i, (vanish_ideal R (f i)).carrier ⊆ P.1.carrier), from 
      begin 
        intros elPI i, apply el_zero_inc_prime, rwr Zcl_to_ZV_eq (f i) (clfI i), 
        exact elPI i 
      end,
    have imp4 : (∀ i, (vanish_ideal R (f i)).carrier ⊆ P.1.carrier)
                   -> (∀ i, P ∈ f i), from 
      begin 
        intros ssPI i, rwr <- Zcl_to_ZV_eq (f i) (clfI i), apply inc_prime_el_zero, 
        exact ssPI i 
      end,
    have imp5 : (∀ i, (vanish_ideal R (f i)).carrier ⊆ P.1.carrier) -> 
                (zero_locus_pred R (ideal_isum I (vanish_ideal R ∘ f)) P), from 
      begin intro IssVIP, apply prop_to_prop_resize, apply ideal_isum_inc, assumption end,
    have imp6 : (zero_locus_pred R (ideal_isum I (vanish_ideal R ∘ f)) P) ->
                (∀ i, (vanish_ideal R (f i)).carrier ⊆ P.1.carrier), from 
      begin
        intros IssP i, 
        apply subset_trans _ (ideal_isum I (vanish_ideal R ∘ f)).carrier _, 
        { apply ideal_inc_isum (vanish_ideal R ∘ f) i },
        { exact prop_resize_to_prop IssP }
      end,  
    apply prop_iff_eq,  
    { intro H, apply imp2, apply imp4, exact imp6 H },
    { intro H, apply imp5, apply imp3, exact imp1 H } }
end                          

@[hott]
def Zariski_topology (R : CommRing) : topological_space (pred_Set (prime_spectrum R)) :=
  topological_space.of_closed (pred_Set (prime_spectrum R)) 
          (@is_Zariski_closed R) (empty_Zariski_closed R)
          (union_Zariski_closed R) (inter_Zariski_closed R)

end algebraic_geometry

end hott