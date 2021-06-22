import rings.basic pathover2

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra hott.subset is_trunc

namespace algebra

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
@[hott]
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
  { exact N₁ ∩ N₂ },
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
begin
  fapply is_set.mk, intros I J p q,
  hinduction p, hinduction I,
  have inj : Π I : Ideal R, I = Ideal.mk I.carrier I.str, from
    begin intro I, hinduction I, refl end,
  rwr apdd_inj_eq Ideal.mk Ideal.to_Subset Ideal.to_str inj q,
  rwr apdd_inj_eq Ideal.mk Ideal.to_Subset Ideal.to_str inj 
                  (refl (Submodule.mk carrier str)), 
  apply ap (λ q, concat q (inj (Ideal.mk carrier str))⁻¹),
  apply ap (concat (inj (Ideal.mk carrier str))), 
  fapply apdd (apdd Ideal.mk),
  { apply is_set.elim },                 
  { apply pathover_of_tr_eq, apply is_prop.elim }
end  

@[hott]
def Ideal_Set (R : CommRing) : Set := 
  Set.mk (Ideal R) (Ideal_is_set R)

@[hott]
instance Ideal_to_Subset {R : CommRing} :
  has_coe (Ideal_Set R) (Subset (ring_as_module R).carrier) :=
⟨λ I, I.carrier⟩

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
  λ I, prop_ulift (Prop.mk (is_prime I) (is_prime_is_prop I))

@[hott]
def prime_pred_prime {R : CommRing} (P : Ideal_Set R) : 
  is_prime_pred P -> is_prime P :=
assume H, prop_ulift_inv (Prop.mk (is_prime P) (is_prime_is_prop P)) H

@[hott]
def PrimeIdeal_Set (R : CommRing) : Set :=
  ↥{P ∈ (Ideal_Set R) | is_prime_pred P}  

@[hott]
instance PrimeIdeal_to_Subset {R : CommRing} :
  has_coe (PrimeIdeal_Set R) (Subset (ring_as_module R).carrier) :=
⟨λ P, (Subset.map _ P).carrier⟩

@[hott]
def proper_prime_ideal {R : CommRing} (P : PrimeIdeal_Set R) : 
  Not ((R•1).carrier ⊆ ↑P) :=
begin
  have prime_P: is_prime (Subset.map _ P), from 
    prime_pred_prime _ ((pred_elem (Subset.map _ P)).1 (obj_elem P)),
  have one_el : ↥((1:R)∈((R•1).carrier)), from all_elem 1,
  intro el, apply empty.elim, 
  apply prime_P.ne_all, exact el _ one_el
end     

@[hott]
def inter_prime {R : CommRing} (P : PrimeIdeal_Set R) (I J : Ideal_Set R) :
  (I ∩ J).carrier ⊆ ↑P <-> I.carrier ⊆ ↑P or J.carrier ⊆ ↑P :=
begin  
  apply pair, 
  { intro inter_ss, sorry },
  { sorry }
end    

end algebra

end hott