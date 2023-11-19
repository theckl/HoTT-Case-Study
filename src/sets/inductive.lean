import sets.finite

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc trunc subset hott.sigma

namespace set

@[hott]
def fin_dep_map_of_list (l : list (Σ (A : Type _), A)) : 
  Π (m : fin_Set l.length), (list_nth_le l m.1 m.2).1 :=
λ m, (list_nth_le l m.1 m.2).2

/- An inductive structure on a type `A` consists of finitely many operations of arbitrary 
   arity which satisfy an induction principle on `A` together with an eliminator. -/
@[hott]
class has_ind_structure (A : Type _) :=
  (ops : list (Σ (op_ar : ℕ), (fin_Set op_ar -> A) -> A))
  (ind : Π {C : A -> Type _}, 
           (Π (m : fin_Set ops.length) (args : fin_Set (list_nth_le ops m.1 m.2).1 -> A),
              (Π k, C (args k)) -> C ((list_nth_le ops m.1 m.2).2 args)) -> Π (a : A), C a)
  (elim : Π {C : A -> Type _} 
            (ih : Π (m : fin_Set ops.length) 
                    (args : fin_Set (list_nth_le ops m.1 m.2).1 -> A),
                    (Π k, C (args k)) -> C ((list_nth_le ops m.1 m.2).2 args)) 
            (m : fin_Set ops.length) (args : fin_Set (list_nth_le ops m.1 m.2).1 -> A)
            (f : Π k, C (args k)), 
            @ind C ih ((list_nth_le ops m.1 m.2).2 args) = ih m args f)

/- If the inductive construction contains no operation at all, or no constant (= operation
   with arity 0), `A` is empty. -/

@[hott, instance]
def nat_is_ind_str : has_ind_structure ℕ :=
begin
  fapply has_ind_structure.mk,
    exact [⟨0, λ arg, 0⟩, ⟨1, λ arg, nat.succ (arg ⟨0,nat.zero_lt_succ 0⟩)⟩],
    intros C ih n, hinduction n,
    { fapply ih ⟨0, nat.zero_lt_succ 1⟩ (λ arg, 0), intro k, 
      hinduction nat.not_lt_zero k.1 k.2 }, 
    { fapply ih ⟨1, nat.le_refl 2⟩ (fin_map_of_list [n]), intro k,
      change Σ (m : ℕ), m < 1 at k, 
      have p : k = ⟨0, nat.zero_lt_succ 0⟩, from 
      begin
        hinduction k, fapply sigma_eq, 
          exact nat.eq_zero_of_le_zero' (nat.le_of_succ_le_succ snd), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _
      end,
      rwr p, exact ih_1 },
   { intros C ih m args f, sorry }
end  

@[hott, instance]
def ind_set_is_dec (A : Set) [H : has_ind_structure A] : decidable_eq A :=
  sorry

end set

end hott