import sets.finite

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc trunc subset hott.sigma

namespace set

/- An inductive structure on a set `A` consists of finitely many operations of arbitrary 
   arity which satisfy an induction principle on `A`. -/
@[hott]
class has_ind_structure (A : Set) :=
  (num_op : ℕ)
  (op_ar : fin_Set num_op -> ℕ)
  (op : Π m : fin_Set num_op, (fin_Set (op_ar m) -> A) -> A)
  (ind : Π {C : A -> Type _}, (Π (m : fin_Set num_op) (ops : fin_Set (op_ar m) -> A),
                                 (Π k : fin_Set (op_ar m), C (ops k)) -> C (op m ops)) ->
                              Π (a : A), C a)

/- If the inductive construction contains no operation at all, or no constant (= operation
   with arity 0), `A` is empty. -/

#reduce (fin_map_of_list [0,1]) ⟨1,_⟩

@[hott, instance]
def nat_is_ind_str : has_ind_structure nat_Set :=
  has_ind_structure.mk 2 (fin_map_of_list [0,1]) 1 
                       (fin_map_of_list [dpair 1 (nat.le_refl 1)])  

@[hott, instance]
def ind_set_is_dec (A : Set) [H : has_ind_structure A] : decidable_eq A :=
  sorry

end set

end hott