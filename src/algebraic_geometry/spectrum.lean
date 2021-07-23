import rings.modules topology.basic

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.set hott.subset hott.trunc

namespace algebraic_geometry

set_option pp.universes true

/- The prime spectrum of a ring `R` is the set of prime ideals of `R`. -/
@[hott]
def prime_spectrum (R : CommRing) := PrimeIdeal_Set R

/- We introduce the zero locus and the vanishing ideal and show some relations. -/
@[hott]
def zero_locus_pred (R : CommRing) : 
  Ideal_Set R -> Setpred ↥(prime_spectrum R) :=
λ I P, prop_resize (I.carrier ⊆ P.1.carrier)

@[hott, reducible]
def zero_locus {R : CommRing} : Ideal_Set R -> Subset ↥(prime_spectrum R) :=
  λ I, pred_to_sset (zero_locus_pred R I)

@[hott]
def is_Zariski_closed {R : CommRing} : Subset ↥(prime_spectrum R) -> Prop :=
  λ Z, image (zero_locus_pred R) (sset_to_pred Z)

@[hott]
def zero_pred_zero {R : CommRing} (I : Ideal R) (U : Subset ↥(prime_spectrum R)) :
  zero_locus_pred R I = sset_to_pred U -> zero_locus I = U :=
begin  
  intro H, 
  apply (sset_eq_iff_inclusion (zero_locus I) U).2, fapply pair,
  { intros P Pz, change ↥(sset_to_pred U P), rwr <- (homotopy_of_eq H P), 
    exact elem_to_pred P Pz },
  { intros P PU, apply pred_to_elem P, change ↥(zero_locus_pred R I P), 
    rwr H, assumption }
end  

@[hott]
def inc_prime_el_zero {R : CommRing} (I : Ideal R) (P : (prime_spectrum R).carrier) :
  I.carrier ⊆ P.1.carrier -> P ∈ zero_locus I :=
begin 
  intro ss_IP, 
  change ↥(sset_to_pred (pred_to_sset (zero_locus_pred R I)) P), 
  apply pred_to_elem P, exact prop_to_prop_resize ss_IP
end    

@[hott]
def el_zero_inc_prime {R : CommRing} (I : Ideal R) (P : (prime_spectrum R).carrier) :
  P ∈ zero_locus I -> I.carrier ⊆ P.1.carrier :=
begin 
  intro elP, 
  exact prop_resize_to_prop (elem_to_pred P elP)
end

@[hott]
def ideal_inc_to_zero_inc {R : CommRing} (I J : Ideal R) :
  I.carrier ⊆ J.carrier -> zero_locus J ⊆ zero_locus I :=
begin  
  intros IJ P, 
  change sset_to_pred (pred_to_sset (zero_locus_pred R J)) P ->
                     sset_to_pred (pred_to_sset (zero_locus_pred R I)) P,
  intro PJ, apply pred_to_elem P,
  exact prop_to_prop_resize (sset_trans IJ (prop_resize_to_prop (elem_to_pred P PJ)))
end    

@[hott]
def zero_ideal_isum {R : CommRing} {I : Set} (f : I -> Ideal_Set R) : 
  ∀ P : (prime_spectrum R).carrier, P ∈ (zero_locus (ideal_isum I f)) <-> 
                                                   P ∈ (⋂ᵢ ((@zero_locus R) ∘ f)) :=
begin
  intro P, fapply pair, 
  { intro elP, let incP := el_zero_inc_prime (ideal_isum I f) P elP, 
    apply (pred_elem P).2, apply prop_to_prop_resize, intro i, apply (pred_elem P).2, 
    exact prop_to_prop_resize (sset_trans (ideal_inc_isum f i) incP) },
  { intros elP, apply (pred_elem P).2, 
    let ssP := (pred_elem P).1 elP, apply prop_to_prop_resize, apply ideal_isum_inc, 
    intro i, apply el_zero_inc_prime, 
    exact (prop_resize_to_prop ssP) i }   
end

@[hott]
def vanish_ideal (R : CommRing) : Subset ↥(prime_spectrum R) -> Ideal_Set R :=
  assume U, submodule_sInter (@ss_Image ↥(prime_spectrum R) (Ideal_Set R) 
                                                             (PrimeIdeal_Set R).map U)

@[hott]
def prime_vanish_inc {R : CommRing} {U : Subset ↥(prime_spectrum R)} 
  (P : (prime_spectrum R).carrier) : P ∈ U -> (vanish_ideal R U).carrier ⊆ P.1.carrier :=
assume elPU, submod_sInter_inc _ P.1 (ss_image_el _ _ P elPU)   

def zero_pred_vanish {R : CommRing} (I : Ideal_Set R) (U : Subset ↥(prime_spectrum R)) :
  (zero_locus_pred R I = sset_to_pred U) -> (I.carrier ⊆ (vanish_ideal R U).carrier) :=
begin  
  intro pred_eq, apply sset_sInter, intros C elC,
  let elC' := (@ss_im_comp (PrimeIdeal_Set R).carrier (Ideal_Set R) 
    (𝒫 (ring_as_module R).carrier) (PrimeIdeal_Set R).map Submodule.to_Subset U C).1 elC,
  let imP := ss_im_preim_el _ U C elC',
  hinduction imP with H, let P := H.1, rwr <- H.2.2, 
  change ↥(I.carrier⊆P.1.carrier), 
  have elP : ↥(P ∈ zero_locus I), by rwr zero_pred_zero I U pred_eq; exact H.2.1,
  exact prop_resize_to_prop ((pred_elem P).1 elP)   
end    

@[hott]
def Zcl_to_ZV_eq {R : CommRing} (U : Subset ↥(prime_spectrum R)) : 
  is_Zariski_closed U -> (zero_locus (vanish_ideal R U) = U) :=
begin
  intro ZclU, hinduction ZclU with fibU, let I := fibU.1,
  apply (sset_eq_iff_inclusion (zero_locus (vanish_ideal R U)) U).2, fapply pair, 
  { rwr <- zero_pred_zero I U fibU.2, 
    apply ideal_inc_to_zero_inc, rwr zero_pred_zero I U fibU.2,
    exact zero_pred_vanish I U fibU.2 },
  { intros P elP, apply (pred_elem P).2, 
    exact prop_to_prop_resize (prime_vanish_inc P elP) }
end     

@[hott]
def ZV_eq_to_Zcl {R : CommRing} (U : Subset ↥(prime_spectrum R)) : 
  (zero_locus (vanish_ideal R U) = U) -> is_Zariski_closed U :=
begin  
  intro ZVU, apply tr, fapply fiber.mk, 
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
  is_Zariski_closed (empty_Subset (prime_spectrum R).carrier) :=
begin 
  apply tr, 
  have all_empty : zero_locus_pred R (R•1) = 
                   (sset_to_pred (empty_Subset ↥(prime_spectrum R))), from 
    begin 
      apply eq_of_homotopy, intro P, 
      change prop_resize ((R•1).carrier ⊆ P) =
                          (sset_to_pred (empty_Subset ↥(prime_spectrum R)) P),                    
      rwr Not_eq_False (empty_not_elem P), rwr <- pr_rinv False, 
      apply ap prop_resize, rwr False_ulift_eq, 
      exact Not_eq_False (@proper_prime_ideal R ↑P (prime_is_prime P)) 
    end,
  exact ⟨R•1, all_empty⟩
end 

@[hott]
def union_Zariski_closed (R : CommRing.{u}) : Π U V : Subset ↥(prime_spectrum R), 
  is_Zariski_closed U -> is_Zariski_closed V -> is_Zariski_closed (U ∪ V) :=
begin  
  intros U V clU clV, hinduction clU with IU, hinduction clV with IV, apply tr,
  have union_inter : zero_locus_pred R (ideal.inter IU.1 IV.1) = (sset_to_pred (U ∪ V)), from
    begin
      apply eq_of_homotopy, intro P, 
      change prop_resize.{0 u} ((IU.point.carrier ∩ IV.point.carrier) ⊆ 
                                    (((PrimeIdeal_Set.{u} R).map P).carrier)) = P∈(U ∪ V),
      rwr ap prop_resize.{0 u} 
               (prop_iff_eq (inter_prime.{0 u} _ IU.1 IV.1 (prime_is_prime P)).1 
                            (inter_prime.{0 u} _ IU.1 IV.1 (prime_is_prime P)).2),
      have P_uo_eq : P ∈ (U ∪ V) = (P ∈ U or P ∈ V), from
        prop_iff_eq (pred_elem P).1 (pred_elem P).2, 
      rwr P_uo_eq, rwr prop_resize_or.{u u 0}, 
      change ((zero_locus_pred R _ P) or (zero_locus_pred R _ P)) = (P∈U or P∈V),
      rwr homotopy_of_eq IU.2 P, rwr homotopy_of_eq IV.2 P
    end,
  exact ⟨ideal.inter IU.1 IV.1, union_inter⟩
end    

@[hott]
def inter_Zariski_closed (R : CommRing) : 
  ∀ (I : Set) (f : I -> 𝒫 ↥(prime_spectrum R)), 
          (∀ i : I, is_Zariski_closed (f i)) -> is_Zariski_closed (⋂ᵢ f) :=
begin 
  intros I f clfI, 
  apply tr, fapply fiber.mk,  
  { exact ideal_isum I ((vanish_ideal R) ∘ f) },
  { apply eq_of_homotopy, intro P, 
    change zero_locus_pred R (ideal_isum I (vanish_ideal R ∘ f)) P = P ∈ (⋂ᵢ f),
    have imp1 : P ∈ (⋂ᵢ f) -> to_Prop (∀ i, P ∈ f i), from 
      assume elP, prop_resize_to_prop (elem_to_pred P elP),
    have imp2 : to_Prop (∀ i, P ∈ f i) -> P ∈ (⋂ᵢ f), from 
      assume elPi, pred_to_elem P (prop_to_prop_resize elPi),
    rwr prop_iff_eq imp1 imp2, clear imp1 imp2,
    have imp3 : to_Prop (∀ i, P ∈ f i) -> to_Prop (∀ i, (vanish_ideal R (f i)).carrier ⊆
                                                ((PrimeIdeal_Set R).map P).carrier), from 
      sorry,
    have imp4 : (∀ i, (vanish_ideal R (f i)).carrier ⊆ ((PrimeIdeal_Set R).map P).carrier)
         -> (∀ i, P ∈ f i), from 
      sorry,
    rwr prop_iff_eq imp3 imp4, clear imp3 imp4,  
    sorry }
end                          

@[hott]
def Zariski_topology (R : CommRing) : topological_space ↥(prime_spectrum R) :=
  topological_space.of_closed ↥(prime_spectrum R) 
          (@is_Zariski_closed R) (empty_Zariski_closed R)
          (union_Zariski_closed R) (inter_Zariski_closed R)

end algebraic_geometry

end hott