import sets.finite

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc trunc subset hott.sigma

namespace set

@[hott]
class has_ind_structure (A : Set) :=
  (num_const : Σ n : ℕ, n ≥ 1)
  (const : fin_Set num_const.1 -> A)
  (num_op_const : ℕ)
  (op_const_ar : fin_Set num_op_const -> Σ n : ℕ, n ≥ 1)
  (op_const : Π m : fin_Set num_op_const, (fin_Set (op_const_ar m).1 -> A) -> A)
  (ind : Π {C : A -> Type _}, (Π m : fin_Set num_const.1, C (const m)) ->
           (Π (m : fin_Set num_op_const) (ops : fin_Set (op_const_ar m).1 -> A),
              (Π k : fin_Set (op_const_ar m).1, C (ops k)) -> C (op_const m ops)) ->
           Π (a : A), C a)

@[hott, instance]
def nat_is_ind_str : has_ind_structure nat_Set :=
  has_ind_structure.mk ⟨1,nat.le_refl 1⟩ (fin_map_of_list [0]) 1 
                       (fin_map_of_list [dpair 1 (nat.le_refl 1)])  

@[hott, instance]
def ind_set_is_dec (A : Set) [H : has_ind_structure A] : decidable_eq A :=
  sorry

end set

end hott