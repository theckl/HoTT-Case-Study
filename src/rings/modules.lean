import rings.basic 

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.subset is_trunc trunc

namespace algebra

set_option pp.universes true

@[hott]
structure module_str (R : CommRing) (M : Set) extends ab_group M renaming 
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero inv→neg 
  mul_left_inv→add_left_inv mul_comm→add_comm :=
(smul : R.carrier -> M -> M)  
(smul_assoc : ∀ (r s : R) (m : M), smul r (smul s m) = smul (r * s) m)
(add_smul : ∀ (r s : R) (m : M), smul (r + s) m = 
                                                    add (smul r m) (smul s m))
(smul_add : ∀ (r : R) (m n : M), smul r (add m n) = 
                                                    add (smul r m) (smul r n)) 
(zero_mul : ∀ (m : M), smul 0 m = zero)
(mul_zero : ∀ (r : R), smul r zero = zero)
(one_mul : ∀ m : M, smul 1 m = m)    
/- I don't know why `0` and `+` don't work for `M`. An infix notation for `smul` 
   would exist if we used `has_scalar`. To simplify things we introduce it later. -/                                                                                                   

attribute [class] module_str

/- If we need the category of R-modules we need to change this definition to a 
   structure on the category of Sets. -/
@[hott]
structure Module (R : CommRing) :=
  (carrier : Set)
  (str : module_str R carrier)  

@[hott]
instance Module_to_Set (R : CommRing) : has_coe (Module R) Set :=
  ⟨λ M : Module R, M.carrier⟩

@[hott]
instance Module_to_Type (R : CommRing) : has_coe_to_sort (Module R) :=
  has_coe_to_sort.mk (Type _) (λ M : Module R, M.carrier)  

@[hott]
instance (R : CommRing) (M : Module R) : module_str R M.carrier := M.str   

@[hott, instance]
def module_add {R : CommRing} {M : Module R} : has_add M :=
⟨M.str.add⟩

/- There is a better palce for this definition and notation. -/
@[hott]
class has_scalar (α β : Type _) := (smul : α -> β -> β)

hott_theory_cmd "local infix `•`:200 := hott.algebra.has_scalar.smul"

@[hott, instance]
def module_smul {R : CommRing} {M : Module R} : has_scalar R M :=
⟨M.str.smul⟩

/- A commutative ring `R` is an `R`-module. -/
@[hott, reducible]
def ring_as_module (R : CommRing) : Module R :=
begin
  fapply Module.mk,
  { exact R.carrier },
  { fapply module_str.mk, 
    { apply_instance }, 
    { exact R.str.add }, 
    { exact R.str.add_assoc }, 
    { exact R.str.zero }, 
    { exact R.str.zero_add }, 
    { exact R.str.add_zero }, 
    { exact R.str.neg }, 
    { exact R.str.add_left_inv }, 
    { exact R.str.add_comm }, 
    { exact R.str.mul }, 
    { intros r s m, 
      change comm_ring.mul r (comm_ring.mul s m) = 
             comm_ring.mul (comm_ring.mul r s) m, rwr R.str.mul_assoc }, 
    { intros r s m, 
      change comm_ring.mul (comm_ring.add r s) m = 
             comm_ring.add (comm_ring.mul r m) (comm_ring.mul s m),
      rwr R.str.right_distrib }, 
    { exact R.str.left_distrib }, 
    { intro m, change 0 * m = 0, rwr ring.zero_mul }, 
    { intro m, change m * 0 = 0, rwr ring.mul_zero }, 
    { exact R.str.one_mul } }
end  

@[hott, reducible]
def ring_to_mod {R : CommRing} (r : R) : ring_as_module R := r

@[hott, reducible]
def mod_to_ring {R : CommRing} (r : ring_as_module R) : R := r 

@[hott]
def rm_mr_inv {R : CommRing} : 
  ∀ r : ring_as_module R, ring_to_mod (mod_to_ring r) = r :=
assume r, rfl 

@[hott]
def mr_rm_inv {R : CommRing} : 
  ∀ r : R, mod_to_ring (ring_to_mod r) = r :=
assume r, rfl 

@[hott]
def rm_mul_smul {R : CommRing} (r s : R) : 
  ring_to_mod (r * s) = r • (ring_to_mod s) :=
rfl  

@[hott]
structure submodule_str {R : CommRing} (M : Module R) (N : Subset M.carrier) :=
  (add_closed : ∀ n₁ n₂ : M, n₁ ∈ N -> n₂ ∈ N -> (n₁ + n₂) ∈ N)
  (smul_closed : ∀ (r : R) (n : M), n ∈ N -> r • n ∈ N)

/- This is a HoTT-ism. -/
@[hott, instance]
def submodule_str_is_prop {R : CommRing} (M : Module R) (N : Subset M.carrier) :
  is_prop (submodule_str M N) :=
begin
  apply is_prop.mk, intros s t, hinduction s, hinduction t, 
  fapply ap011 submodule_str.mk, all_goals { apply is_prop.elim },
end      

/- At some point we may need the module structure on a submodule. -/

@[hott]
structure Submodule (R : CommRing) (M : Module R) :=
  (carrier : Subset M.carrier)
  (str : submodule_str M carrier)

@[hott]
instance Module_to_Subset (R : CommRing) (M : Module R) : 
  has_coe (Submodule R M) (Subset M.carrier) :=
  ⟨λ N : Submodule R M, N.carrier⟩

@[hott]
def Submodule.to_Subset {R : CommRing} {M : Module R} (N : Submodule R M) : Subset M.carrier := 
  N.carrier

@[hott]
def Submodule.to_str {R : CommRing} {M : Module R} (N : Submodule R M) := N.str

/- This is a HoTT-ism. -/
@[hott, instance]
def Submodule_is_set {R : CommRing} (M : Module R): is_set (Submodule R M) :=
begin
  fapply is_set.mk, intros N₁ N₂ p q,
  hinduction p, hinduction N₁,
  have inj : Π N : Submodule R M, N = Submodule.mk N.carrier N.str, from
    begin intro N, hinduction N, refl end,
  rwr apdd_inj_eq Submodule.mk Submodule.to_Subset Submodule.to_str inj q,
  rwr apdd_inj_eq Submodule.mk Submodule.to_Subset Submodule.to_str inj 
                  (refl (Submodule.mk carrier str)), 
  apply ap (λ q, concat q (inj (Submodule.mk carrier str))⁻¹),
  apply ap (concat (inj (Submodule.mk carrier str))), 
  fapply apdd (apdd Submodule.mk),
  { apply is_set.elim },                 
  { apply pathover_of_tr_eq, apply is_prop.elim }
end  

@[hott]
def Submodule_Set {R : CommRing} (M : Module R) : Set := 
  Set.mk (Submodule R M) (Submodule_is_set M)

@[hott]
instance Submodule_to_Subset {R : CommRing} (M : Module R) :
  has_coe (Submodule_Set M) (Subset M.carrier) :=
⟨λ N, N.carrier⟩

@[hott]
def Submodule_Set_to_Subsets {R : CommRing} (M : Module R) :
  Submodule_Set M -> 𝒫 M.carrier :=
assume N, Submodule.to_Subset N   

@[hott]
def module_as_submodule {R : CommRing} (M : Module R) : Submodule R M :=
begin  
  fapply Submodule.mk,
  { exact total_Subset M },
  { fapply submodule_str.mk,
    { intros n₁ n₂ el₁ el₂, 
      change (sset_to_pred (total_Subset M.carrier) (n₁ + n₂)).carrier,
      rwr total_pred (n₁+n₂), exact true.intro },
    { intros r n el_n, 
      change (sset_to_pred (total_Subset M.carrier) (r•n)).carrier,
      rwr total_pred (r•n), exact true.intro } }
end  

@[hott]
protected def submodule.inter {R : CommRing} {M : Module R} 
  (N₁ N₂ : Submodule R M) : Submodule R M :=
begin
  fapply Submodule.mk,
  { exact (Submodule.to_Subset N₁) ∩ (Submodule.to_Subset N₂) },
  { fapply submodule_str.mk,
    { intros n₁ n₂ el₁ el₂, 
      apply (pred_elem (n₁ + n₂)).2, apply pair,  
      { apply N₁.str.add_closed, 
        { exact ((pred_elem n₁).1 el₁).1 },
        { exact ((pred_elem n₂).1 el₂).1 } },
      { apply N₂.str.add_closed, 
        { exact ((pred_elem n₁).1 el₁).2 },
        { exact ((pred_elem n₂).1 el₂).2 } } },
    { intros r n el, 
      apply (pred_elem (r•n)).2, apply pair, 
      { apply N₁.str.smul_closed, exact ((pred_elem n).1 el).1 },
      { apply N₂.str.smul_closed, exact ((pred_elem n).1 el).2 } } }
end  

@[hott, instance]
def submodule_inter {R : CommRing} {M : Module R} : 
  has_inter (Submodule R M) :=
⟨submodule.inter⟩

@[hott]
def submodule_sInter {R : CommRing} {M : Module R} (S : Subset (Submodule_Set M)) :
  Submodule R M :=
begin
  fapply Submodule.mk,
  { exact ⋂₀ (@ss_Image (Submodule_Set M) (𝒫 M.carrier) 
                                   (@Submodule.to_Subset R M) S) },
  { have B_str : Π B : 𝒫 M.carrier, 
      (B∈@ss_Image (Submodule_Set M) (𝒫 M.carrier) (@Submodule.to_Subset R M) S) -> 
                                                               submodule_str M B, from
      begin 
        intros B B_im, 
        have ex_B_str : ↥(image ((@Submodule.to_Subset R M) ∘ S.map) B), from 
          @ss_image_preimage (Submodule_Set M) (𝒫 M.carrier) 
                                                     (@Submodule.to_Subset R M) S B B_im,
        hinduction ex_B_str with fB, rwr <- fB.2, exact (S.map fB.1).str 
        end,                                                             
    fapply submodule_str.mk,
    { intros n₁ n₂ el1 el2, 
      apply (pred_elem (n₁+n₂)).2, 
      apply prop_to_prop_resize, intros B B_im, 
      have el1_B : ↥(n₁ ∈ B), from prop_resize_to_prop ((pred_elem n₁).1 el1) B B_im,
      have el2_B : ↥(n₂ ∈ B), from prop_resize_to_prop ((pred_elem n₂).1 el2) B B_im,
      exact (B_str B B_im).add_closed n₁ n₂ el1_B el2_B },
    { intros r n el, apply (pred_elem (r•n)).2, 
      apply prop_to_prop_resize, intros B B_im,
      have el_B : ↥(n ∈ B), from prop_resize_to_prop ((pred_elem n).1 el) B B_im,
      exact (B_str B B_im).smul_closed r n el_B } }
end  

@[hott]
def submod_sInter_inc {R : CommRing} {M : Module R} (S : Subset (Submodule_Set M)) :
  ∀ N : Submodule_Set M, N ∈ S -> (submodule_sInter S).carrier ⊆ N.carrier :=
assume N elN, sInter_sset (@ss_Image (Submodule_Set M) (𝒫 M.carrier) 
                              (@Submodule.to_Subset R M) S) N.carrier (ss_image_el _ _ N elN)

@[hott]
def submodule_span {R : CommRing} {M : Module R} (S : Subset M.carrier) : 
  Submodule R M :=
submodule_sInter {N ∈ Submodule_Set M | S ⊆ (@Submodule.to_Subset R M N) } 

@[hott]
def submod_gen_inc_span {R : CommRing} {M : Module R} (S : Subset M.carrier) : 
  S ⊆ (submodule_span S).carrier :=
begin
  apply sset_sInter,
  intros C elC, let el_imC := ss_im_preim_el _ _ _ elC, hinduction el_imC with el_imC',
  let N := el_imC'.1, rwr <- el_imC'.2.2,
  exact (pred_elem N).1 el_imC'.2.1
end    

@[hott]
def submod_gen_span_inc {R : CommRing} {M : Module R} (S : Subset M.carrier) 
  (N : Submodule_Set M) : S ⊆ N.carrier -> (submodule_span S).carrier ⊆ N.carrier :=
begin
  let Sss := {N ∈ Submodule_Set M | S ⊆ (@Submodule.to_Subset R M N) },
  intro ss_SN, exact submod_sInter_inc Sss N ((pred_elem N).2 ss_SN)
end  

@[hott]
def submodule_ssum {R : CommRing} {M : Module R} (S : Subset (Submodule_Set M)) :
  Submodule R M :=
submodule_span ⋃₀ (@ss_Image (Submodule_Set M) (𝒫 M.carrier) 
                                                          (@Submodule.to_Subset R M) S)  

@[hott]
def submodule_isum {R : CommRing} {M : Module R} {I : Set} 
  (f : I -> Submodule_Set M) : Submodule R M :=
submodule_span ⋃ᵢ ((@Submodule.to_Subset R M) ∘ f)  

@[hott]
def submodule_inc_isum {R : CommRing} {M : Module R} {I : Set} 
  (f : I -> Submodule_Set M) : ∀ i : I, (f i).carrier ⊆ (submodule_isum f).carrier :=
begin 
  intro i, 
  fapply @sset_trans M.carrier _ (⋃ᵢ ((@Submodule.to_Subset R M) ∘ f)) _, 
  { exact sset_iUnion ((@Submodule.to_Subset R M) ∘ f) i }, 
  { exact submod_gen_inc_span ⋃ᵢ ((@Submodule.to_Subset R M) ∘ f) } 
end  

@[hott]
def submodule_isum_inc {R : CommRing} {M : Module R} {I : Set} 
  (f : I -> Submodule_Set M) (N : Submodule R M) : 
  (∀ i : I, (f i).carrier ⊆ N.carrier) -> (submodule_isum f).carrier ⊆ N.carrier :=
begin 
  intro Iss, apply submod_gen_span_inc, 
  exact iUnion_sset (Submodule.to_Subset ∘ f) N.carrier Iss 
end    

/- Ideals are defined as submodules of the ring as a module over itself. -/
@[hott]
def Ideal (R : CommRing) := Submodule R (ring_as_module R)  

@[hott]
def Ideal.mk {R : CommRing} : Π (I : Subset (ring_as_module R).carrier) 
  (str : submodule_str (ring_as_module R) I), Ideal R :=
λ I str, Submodule.mk I str  

@[hott]
def Ideal.to_Subset {R : CommRing} (I : Ideal R) := I.carrier

@[hott]
def Ideal.to_str {R : CommRing} (I : Ideal R) := I.str

@[hott]
def all_Ideal (R : CommRing) : Ideal R :=
  module_as_submodule (ring_as_module R)  

notation R`•1` := all_Ideal R 

/- This is a HoTT-ism. -/
@[hott, instance]
def Ideal_is_set (R : CommRing) : is_set (Ideal R) :=
  Submodule_is_set (ring_as_module R)

@[hott]
def Ideal_Set (R : CommRing) : Set := 
  Set.mk (Ideal R) (Ideal_is_set R)

@[hott]
instance Ideal_to_Subset {R : CommRing} :
  has_coe (Ideal_Set R) (Subset (ring_as_module R).carrier) :=
⟨λ I, I.carrier⟩

@[hott]
def ideal_span {R : CommRing} (S : Subset (ring_as_module R).carrier) : Ideal R :=
  submodule_span S

@[hott]
def ideal_ssum {R : CommRing} (S : Subset (Ideal_Set R)) : Ideal R :=
  submodule_ssum S

@[hott]
def ideal_isum {R : CommRing} (I : Set) (f : I -> Ideal_Set R) : Ideal R :=
  submodule_isum f  

@[hott]
def ideal_inc_isum {R : CommRing} {I : Set} 
  (f : I -> Ideal_Set R) : ∀ i : I, (f i).carrier ⊆ (ideal_isum I f).carrier := 
λ i, submodule_inc_isum f i 

@[hott]
def ideal_isum_inc {R : CommRing} {I : Set} 
  (f : I -> Ideal_Set R) (N : Ideal R) : 
  (∀ i : I, (f i).carrier ⊆ N.carrier) -> (ideal_isum I f).carrier ⊆ N.carrier :=
λ Iss, submodule_isum_inc f N Iss  

@[hott, reducible]
protected def ideal.inter {R : CommRing} (I J : Ideal R) : Ideal R :=
  submodule.inter I J

@[hott, instance]
def ideal_inter {R : CommRing} : has_inter (Ideal_Set R) :=
  ⟨ideal.inter⟩

@[hott]
structure is_prime {R : CommRing} (P : Ideal R) :=
  (ne_all : ¬((1:R) ∈ P.carrier))
  (mem_or_mem : ∀ r s : R, r * s ∈ P.carrier -> 
                           ((r ∈ P.carrier) or (s ∈ P.carrier)))

/- This is a HoTT-ism. -/
@[hott, instance]
def is_prime_is_prop {R : CommRing} (P : Ideal R) : is_prop (is_prime P) :=
begin
  fapply is_prop.mk, intros P Q,
  hinduction P, hinduction Q, apply ap011, all_goals { apply is_prop.elim }
end

@[hott]
def is_prime_pred {R : CommRing} : Setpred (Ideal_Set R) :=
  λ I, Prop.mk (is_prime I) (is_prime_is_prop I)

@[hott]
def prime_pred_prime {R : CommRing} (P : Ideal_Set R) : 
  is_prime_pred P -> is_prime P :=
assume H, H

@[hott]
def PrimeIdeal_Set (R : CommRing) :=
  {P ∈ (Ideal_Set R) | is_prime_pred P}  

@[hott]
def proper_prime_ideal {R : CommRing} (P : Ideal_Set R) : 
  @is_prime R P -> Not ((R•1).carrier ⊆ P.carrier) :=
begin
  intro prime_P,
  have one_el : ↥((1:R)∈((R•1).carrier)), from all_elem 1,
  intro el, apply empty.elim, 
  apply prime_P.ne_all, exact el _ one_el
end     

@[hott]
def inter_prime {R : CommRing} (P : Ideal_Set R) (I J : Ideal_Set R) 
  (prime_P : is_prime P) :
  (I.carrier ∩ J.carrier) ⊆ P.carrier <-> 
                                      I.carrier ⊆ P.carrier or J.carrier ⊆ P.carrier :=
begin  
  apply pair, 
  { apply (contrapos _ _).2, intro nor, 
    rwr prop_iff_eq (not_or _ _).1 (not_or _ _).2 at nor, 
    rwr prop_iff_eq (not_ss_elem _ _).1 (not_ss_elem _ _).2 at nor,
    rwr prop_iff_eq (not_ss_elem _ _).1 (not_ss_elem _ _).2 at nor,
    hinduction nor.1 with tr1 cons1, hinduction nor.2 with tr2 cons2, 
    clear tr1 tr2 nor,
    hinduction cons1 with r₁ Pr1, hinduction cons2 with r₂ Pr2,
    apply (not_ss_elem _ _).2, 
    let r := mod_to_ring r₁, let s := mod_to_ring r₂, 
    let rs := ring_to_mod (comm_ring.mul r s),
    have eI : ring_to_mod (comm_ring.mul r s) = s • r₁, 
      by rwr R.str.mul_comm; rwr rm_mul_smul r s; rwr rm_mr_inv,
    have eJ : ring_to_mod (comm_ring.mul r s) = r • r₂, 
      by change ring_to_mod (r * s) = r•r₂; rwr rm_mul_smul r s; rwr rm_mr_inv,
    have el : ↥(rs ∈ (I.carrier ∩ J.carrier)), from 
      begin  
        apply (pred_elem (ring_to_mod (comm_ring.mul r s))).2, apply pair, 
        { rwr eI, apply I.str.smul_closed, exact Pr1.1 },
        { rwr eJ, apply J.str.smul_closed, exact Pr2.1 }
      end,   
    have nel : ↥(Not (rs ∈ P.carrier)), from 
      begin  
        intro el_rs, hinduction prime_P.mem_or_mem r s el_rs with tr_or r_or_s, 
        clear tr_or, hinduction r_or_s with elr els, 
        { exact Pr1.2 elr },
        { exact Pr2.2 els }
      end,
    exact tr (construct_elem.intro rs ⟨el, nel⟩) },
  { intro I_or_J, hinduction I_or_J with tr_or, hinduction tr_or with Iss Jss, 
    { exact sset_trans (inter_sset_l I.carrier J.carrier) Iss },
    { exact sset_trans (inter_sset_r I.carrier J.carrier) Jss } }
end    

end algebra

end hott