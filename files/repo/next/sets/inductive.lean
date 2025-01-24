import sets.finite

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc trunc subset hott.sigma

namespace set

@[hott]
inductive args (α : Type u) : ℕ -> Type u 
| nil {} : args 0
| cons {n : ℕ} (a : α) (v : args n) : args (n+1) 

@[hott]
def largs (α : Type u) : Π (l : list α), args α l.length :=
begin
  intro l, hinduction l,
    change args α 0, exact args.nil,
    change args α (tl.length + 1), exact args.cons hd ih
end

@[hott]
def argsl {α : Type _} {n : ℕ} : args α n -> list α :=
begin 
  intro v, hinduction v, 
    exact [],
    exact a :: ih
end  

@[hott]
def args_hd {α : Type _} [inhabited α] {n : ℕ} : args α n -> α :=
begin
  intro v, hinduction v,
  exact default α,
  exact a
end

@[hott]
def args_tl {α : Type _} {n : ℕ} : args α n -> args α (nat.pred n) :=
begin
  intro v, hinduction v,
  exact args.nil,
  exact v
end

@[hott]
def v : args ℕ 3 :=
  largs ℕ [1,2,3]

@[hott]
def args.argD {α : Type _} [inhabited α] {n : ℕ} : args α n -> ℕ -> α :=
begin  
  intros v, hinduction v,
    intro i, exact default α,
    intro i, exact ite (i < n+1) (ite (i = 0) a (ih (nat.pred i))) 
                                 (default α)
end

@[hott]
def fun_args (α β : Type _) (ar : ℕ) := (args α ar) -> β

@[hott]
def operation (α : Type u) (ar : ℕ) := fun_args α α ar

@[hott]
def fun_no_arg (α β : Type _) : β -> fun_args α β 0 :=
  λ b : β, λ a : args α 0, b

@[hott]
def fun_add_arg {α β : Type _} [inhabited α] (ar : ℕ) : 
  (α -> (fun_args α β ar)) -> fun_args α β (ar+1) :=
λ f args, f (args_hd args) (args_tl args)

@[hott]
def nat_zero : fun_args ℕ ℕ 0  := fun_no_arg ℕ ℕ 0

@[hott]
def nat_succ : fun_args ℕ ℕ 1 := fun_add_arg 0 (λ n, fun_no_arg ℕ ℕ (n+1))


@[hott]
def fin_dep_map_of_fin_map {n : ℕ} (f : fin_Set n -> (Σ (A : Type _), A)) :
  Π (m : fin_Set n), (f m).1 :=
λ m, (f m).2  

@[hott]
def fin_dep_map_of_list (l : list (Σ (A : Type _), A)) : 
  Π (m : fin_Set l.length), (list_nth_le l m.1 m.2).1 :=
fin_dep_map_of_fin_map (fin_map_of_list l)

/- An inductive structure on a type `A` consists of finitely many operations of arbitrary 
   arity which satisfy an induction principle on `A` together with an eliminator. -/
@[hott]
class has_ind_structure (A : Type _) :=
  (ops : list (operation A))
  (ind : Π {C : A -> Type _}, 
           (Π (m : fin_Set ops.length) (v : args A (list_nth_le ops m.1 m.2).1),
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
      have p : k = ⟨0, nat.zero_lt_succ 0⟩, from 
      begin
        hinduction k, fapply sigma_eq, 
          exact nat.eq_zero_of_le_zero' (nat.le_of_succ_le_succ snd), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _
      end,
      rwr p, exact ih_1 },
   intros C ih m args f, change ↥(fin_Set 2) at m, sorry 
end  

@[hott, instance]
def ind_set_is_dec (A : Set) [H : has_ind_structure A] : decidable_eq A :=
  sorry

end set

end hott