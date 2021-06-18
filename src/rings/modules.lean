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
instance Ideal_to_Subset (R : CommRing) (I : Ideal R) : 
  has_coe (Ideal R) (Subset R.carrier) :=
  ⟨λ N : Ideal R, N.carrier⟩

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
def PrimeIdeal_Set (R : CommRing) : Set :=
  ↥{P ∈ (Ideal_Set R) | is_prime_pred P}                           

end algebra

end hott