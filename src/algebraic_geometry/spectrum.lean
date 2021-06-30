import rings.modules

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.subset hott.trunc

namespace algebraic_geometry

set_option pp.universes false

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
  have PUI : ∀ (P : (prime_spectrum R).carrier), P ∈ U -> I.carrier ⊆ P.1.carrier, from 
    sorry,
  have imC : ↥(image (Submodule.to_Subset ∘ (@ss_Image.{u+1 u+1} (PrimeIdeal_Set R).carrier 
                                      (Ideal_Set R) (PrimeIdeal_Set R).map U).map) C), from 
    sorry,   
  hinduction imC with fibC, 
  have PC : ↥↥(ss_Image.{u+1 u+1} (PrimeIdeal_Set R).map U), from fibC.1,
  sorry
end    

@[hott]
def ZVZcl_eq_Zcl {R : CommRing} (U : Subset ↥(prime_spectrum R)) : 
  is_Zariski_closed U -> (zero_locus (vanish_ideal R U) = U) :=
begin
  intro ZclU, hinduction ZclU with IU, 
  have IV : ↥(IU.point.carrier ⊆ (vanish_ideal R U).carrier), from sorry,
  apply (sset_eq_iff_inclusion _ _).2, fapply pair, 
  { intro P, 
    change sset_to_pred (pred_to_sset (zero_locus_pred R (vanish_ideal R U))) P -> (P∈U),
    rwr sset_pred_rinv, intro ZVP,
    have lVP : ↥(prop_ulift ((vanish_ideal R U).carrier ⊆ P.1.carrier)), from ZVP,
    have VP : ↥((vanish_ideal R U).carrier ⊆ P.1.carrier), from prop_ulift_inv _ lVP,
    clear ZVP lVP, change ↥(sset_to_pred U P), rwr <- homotopy_of_eq IU.2 P,
    change (prop_ulift (IU.point.carrier ⊆ P.1.carrier)).carrier, apply ulift.up,
    exact sset_trans IV VP },
  { sorry }
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
def inter_Zariski_closed (R : CommRing) : ∀ (I : Set) (f : I -> 𝒫 ↥(prime_spectrum R)), 
                        (∀ i : I, is_Zariski_closed (f i)) -> is_Zariski_closed (⋂ᵢ f) :=
begin 
  intros I f clfI, 
  have ideal_fi : ∀ i : I, fiber (zero_locus_pred R) (sset_to_pred (f i)), from 
    begin intro i, sorry end,
  apply tr, sorry
end                          

end algebraic_geometry

end hott