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
λ I P, prop_ulift (I.carrier ⊆ P.1.carrier)

@[hott, reducible]
def zero_locus {R : CommRing} : Ideal_Set R -> Subset ↥(prime_spectrum R) :=
  λ I, pred_to_sset (zero_locus_pred R I)

@[hott]
def is_Zariski_closed {R : CommRing} : Subset ↥(prime_spectrum R) -> Prop :=
  λ Z, image (zero_locus_pred R) (sset_to_pred Z)

@[hott]
def zero_pred_zero {R : CommRing} (I : Ideal R) (U : Subset ↥(prime_spectrum R)) :
  zero_locus_pred R I = sset_to_pred U -> zero_locus I = U :=
assume H, (ap pred_to_sset H) ⬝ (sset_pred_linv U)

@[hott]
def inc_prime_el_zero {R : CommRing} (I : Ideal R) (P : (prime_spectrum R).carrier) :
  I.carrier ⊆ P.1.carrier -> P ∈ zero_locus I :=
begin 
  intro ss_IP, 
  change ↥(sset_to_pred (pred_to_sset (zero_locus_pred R I)) P),
  rwr sset_pred_rinv, 
  exact ulift.up ss_IP
end    

@[hott]
def el_zero_inc_prime {R : CommRing} (I : Ideal R) (P : (prime_spectrum R).carrier) :
  P ∈ zero_locus I -> I.carrier ⊆ P.1.carrier :=
begin 
  intro elP, 
  let elP' : ↥(sset_to_pred (pred_to_sset (zero_locus_pred R I)) P) := elP,
  rwr sset_pred_rinv at elP', 
  exact ulift.down elP'
end

@[hott]
def ideal_inc_to_zero_inc {R : CommRing} (I J : Ideal R) :
  I.carrier ⊆ J.carrier -> zero_locus J ⊆ zero_locus I :=
begin  
  intros IJ P, 
  change sset_to_pred (pred_to_sset (zero_locus_pred R J)) P ->
                     sset_to_pred (pred_to_sset (zero_locus_pred R I)) P,
  rwr sset_pred_rinv, rwr sset_pred_rinv,
  change prop_ulift (J.carrier ⊆ P.1.carrier) -> prop_ulift (I.carrier ⊆ P.1.carrier),
  intro H, hinduction H with JP, apply ulift.up, exact sset_trans IJ JP
end    

@[hott]
def zero_ideal_ssum {R : CommRing.{u}} {I : Set.{u}} (f : I -> Ideal_Set R) :
  zero_locus (ideal_isum I f) = 
    @iInter ↥(prime_spectrum R) (trunctype_ulift.{u u+1} I) (zero_locus ∘ f ∘ ulift.down) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, fapply pair, 
  { intros P elP, let incP := el_zero_inc_prime (ideal_isum I f) P elP, 
    apply (pred_elem P).2, intro i, apply (pred_elem P).2, apply ulift.up, 
    exact sset_trans (ideal_inc_isum f (ulift.down i)) incP },
  { intros P elP, apply (pred_elem P).2, apply ulift.up,
    let ssP := (pred_elem P).1 elP, apply ideal_isum_inc, intro i,
    apply el_zero_inc_prime, rwr <- down_up_eq i,
    exact ssP (ulift.up i) }   
end

@[hott]
def vanish_ideal (R : CommRing.{u}) : Subset ↥(prime_spectrum R) -> Ideal_Set R :=
  assume U, submodule_sInter (@ss_Image.{u+1 u+1} ↥(prime_spectrum R) (Ideal_Set R) 
                                                             (PrimeIdeal_Set R).map U)

@[hott]
def prime_vanish_inc {R : CommRing.{u}} {U : Subset ↥(prime_spectrum R)} 
  (P : (prime_spectrum R).carrier) : P ∈ U -> (vanish_ideal R U).carrier ⊆ P.1.carrier :=
assume elPU, submod_sInter_inc _ P.1 (ss_image_el _ _ P elPU)   

def zero_pred_vanish {R : CommRing.{u}} (I : Ideal R) (U : Subset ↥(prime_spectrum R)) :
  (zero_locus_pred R I = sset_to_pred U) -> I.carrier ⊆ vanish_ideal R U :=
begin  
  intro pred_eq, apply sset_sInter, intros C elC,
  rwr @ss_im_comp.{u+1 u+1 u+1} (PrimeIdeal_Set R).carrier (Ideal_Set R) 
      (𝒫 (ring_as_module R).carrier) (PrimeIdeal_Set R).map Submodule.to_Subset U at elC,
  let imP := ss_im_preim_el.{u+1 u+1} _ U C elC,
  hinduction imP with H, let P := H.1, rwr <- H.2.2, 
  change ↥(I.carrier⊆P.1.carrier), 
  have elP : ↥(P ∈ zero_locus I), by rwr zero_pred_zero I U pred_eq; exact H.2.1,
  exact prop_ulift_inv _ ((pred_elem P).1 elP)   
end    

@[hott]
def Zcl_to_ZV_eq {R : CommRing} (U : Subset ↥(prime_spectrum R)) : 
  is_Zariski_closed U -> (zero_locus (vanish_ideal R U) = U) :=
begin
  intro ZclU, hinduction ZclU with fibU, let I := fibU.1,
  apply (sset_eq_iff_inclusion _ _).2, fapply pair, 
  { rwr <- zero_pred_zero I U fibU.2, 
    apply ideal_inc_to_zero_inc, rwr zero_pred_zero I U fibU.2,
    exact zero_pred_vanish I U fibU.2 },
  { intros P elP, apply (pred_elem P).2, 
    exact ulift.up (prime_vanish_inc P elP) }
end     

@[hott]
def ZV_eq_to_Zcl {R : CommRing} (U : Subset ↥(prime_spectrum R)) : 
  (zero_locus (vanish_ideal R U) = U) -> is_Zariski_closed U :=
begin  
  intro ZVU, apply tr, fapply fiber.mk, 
  { exact vanish_ideal R U },
  { apply eq_of_homotopy, intro P, apply prop_iff_eq _ _, 
    { change (prop_ulift ((vanish_ideal R U).carrier ⊆ P.1.carrier)) → (sset_to_pred U P), 
      intro l_ss_VP, rwr <- ZVU, 
      exact inc_prime_el_zero (vanish_ideal R U) P (prop_ulift_inv _ l_ss_VP) },
    { intro elP, exact ulift.up (prime_vanish_inc P elP) } }
end    

/- Now we show the properties needed to construct the Zariski topology from Zariski-closed 
   sets. -/
@[hott]
def empty_Zariski_closed (R : CommRing) : 
  is_Zariski_closed (empty_Subset ↥(prime_spectrum R)) :=
begin 
  apply tr, 
  have all_empty : zero_locus_pred R (R•1) = 
                   (sset_to_pred (empty_Subset ↥(prime_spectrum R))), from 
    begin 
      apply eq_of_homotopy, intro P, 
      change prop_ulift ((R•1).carrier ⊆ P) =
                          (sset_to_pred (empty_Subset ↥(prime_spectrum R)) P),
      rwr Not_eq_False (proper_prime_ideal P), 
      rwr Not_eq_False (empty_not_elem P), exact ulift_False
    end,
  exact ⟨R•1, all_empty⟩
end 

@[hott]
def union_Zariski_closed (R : CommRing) : Π U V : Subset ↥(prime_spectrum R), 
  is_Zariski_closed U -> is_Zariski_closed V -> is_Zariski_closed (U ∪ V) :=
begin  
  intros U V clU clV, hinduction clU with IU, hinduction clV with IV, apply tr,
  have union_inter : zero_locus_pred R (IU.1 ∩ IV.1) = (sset_to_pred (U ∪ V)), from
    begin
      apply eq_of_homotopy, intro P, 
      change prop_ulift ((IU.point ∩ IV.point).carrier ⊆ P) = P∈(U ∪ V),
      rwr prop_iff_eq (inter_prime _ _ _).1 (inter_prime _ _ _).2,
      have P_uo_eq : P ∈ (U ∪ V) = (P ∈ U or P ∈ V), from
        prop_iff_eq (pred_elem P).1 (pred_elem P).2, 
      rwr P_uo_eq, rwr prop_ulift_or, 
      change ((zero_locus_pred R _ P) or (zero_locus_pred R _ P)) = (P∈U or P∈V),
      rwr homotopy_of_eq IU.2 P, rwr homotopy_of_eq IV.2 P
    end,
  exact ⟨IU.1 ∩ IV.1, union_inter⟩
end    

@[hott]
def inter_Zariski_closed (R : CommRing.{u}) : 
  ∀ (I : Set) (f : I -> 𝒫 ↥(prime_spectrum R)), 
          (∀ i : I, is_Zariski_closed (f i)) -> is_Zariski_closed (⋂ᵢ f) :=
begin 
  intros I f clfI, 
  apply tr, fapply fiber.mk,  
  { sorry },
  { sorry }
end                          

@[hott]
def Zariski_topology (R : CommRing) : topological_space ↥(prime_spectrum R) :=
  topological_space.of_closed ↥(prime_spectrum R) 
          (@is_Zariski_closed R) (empty_Zariski_closed R)
          (union_Zariski_closed R) (inter_Zariski_closed R)

end algebraic_geometry

end hott