import rings.basic

universes u u' v w
hott_theory

set_option old_structure_cmd true

namespace hott

open hott.algebra

namespace algebra

@[hott]
structure module (R : CommRing) (M : Set) extends ab_group M renaming 
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero inv→neg 
  mul_left_inv→add_left_inv mul_comm→add_comm :=
(smul : R -> M -> M)  
(smul_assoc : ∀ (r s : R) (m : M), smul r (smul s m) = smul (r * s) m)
(smul_distrib_left : ∀ (r s : R) (m : M), smul (r + s) m = 
                                                    add (smul r m) (smul s m))
(smul_distrib_right : ∀ (r : R) (m n :M), smul r (add m n) = 
                                                    add (smul r m) (smul r n)) 
(zero_mul : ∀ (m : M), smul 0 m = zero)
(mul_zero : ∀ (r : R), smul r zero = zero)
(one_mul : ∀ m : M, smul 1 m = m)    
/- I don't know why `0` and `+` don't work for `M`. An infix notation for `smul` 
   would exist if we used `has_scalar`. To simplify things we introduce it later. -/                                                                                                   

attribute [class] module

@[hott]
structure RingModule (R : CommRing) :=
  (carrier : Set)
  (str : module R carrier)

@[hott]
instance RingModule_to_Set (R : CommRing) : has_coe (RingModule R) Set :=
  ⟨λ M : RingModule R, M.carrier⟩

@[hott]
instance RingModule_to_Type (R : CommRing) : has_coe_to_sort (RingModule R) :=
  has_coe_to_sort.mk (Type _) (λ M : RingModule R, M.carrier)  

@[hott]
instance (R : CommRing) (M : RingModule R) : module R M.carrier := M.str   

end algebra

end hott