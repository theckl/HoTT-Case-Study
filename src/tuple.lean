import hott.init types2 nat2

universes u v w
hott_theory

namespace hott 
open hott.is_trunc hott.is_equiv

@[hott]
structure fin (n : nat) :=
  (val : nat)
  (is_lt : val < n)

@[hott]
def fin_size_eq {n m : ℕ} (H : n = m) : fin n -> fin m :=
  begin intro i, exact fin.mk i.val (H ▸[λ k, i.val < k] i.is_lt) end

@[hott]
def fin_lift {n m : ℕ} : fin n -> fin (n+m) :=
  assume a, ⟨a.1, nat.lt_of_lt_of_le a.2 (nat.le_add_right n m)⟩

@[hott]
def fin_lift_rev {n m : ℕ} : fin m -> fin (n+m) :=
  assume i, fin.mk (n+i.val) (nat.add_lt_add_left i.is_lt n)

@[hott, hsimp]
def fin_desc {n m : ℕ} (i : fin (n+m)) (H : i.1 < n) : fin n :=
  ⟨i.1, H⟩  

@[hott]
def fin_desc_rev {n m : ℕ} (i : fin (n+m)) (H : i.val ≥ n) : fin m :=
  fin.mk (i.val-n) (nat.sub_lt_of_lt_add i.is_lt H)

@[hott]
def fin_eq {n : nat} : Π {i j : fin n}, i.val = j.val -> i = j :=
begin
  intros i j p, hinduction i with i qi, hinduction j with j qj, 
  fapply apd011 fin.mk p, apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott]
def fin_lift_desc {n m : ℕ} (b : fin (n+m)) (H2 : b.1 < n) :
  fin_lift (fin_desc b H2) = b :=
begin apply fin_eq, refl end 

@[hott]
def fin_desc_lift {n m : ℕ} (i : fin n) (H : (@fin_lift n m i).val < n) :
  fin_desc (fin_lift i) H = i :=
begin apply fin_eq, refl end

@[hott]
def fin_lift_desc_rev {n m : ℕ} (i : fin (n+m)) (H2 : i.1 ≥ n) :
  fin_lift_rev (fin_desc_rev i H2) = i :=
begin apply fin_eq, exact nat.add_sub_cancel_left'' n i.val H2 end

@[hott]
def fin_desc_lift_rev {n m : ℕ} (i : fin m) (H : (@fin_lift_rev n m i).val ≥ n) :
  fin_desc_rev (fin_lift_rev i) H = i :=
begin apply fin_eq, exact nat.add_sub_cancel_left' n i.val end


@[hott] 
def tuple (A : Type _) (n : ℕ) := fin n -> A

@[hott]
def tuple_of_list {A : Type _} (l : list A) : tuple A (list.length l) :=
begin 
  induction l,
  { intro i, hinduction nat.not_lt_zero i.val i.is_lt },
  { intro i, hinduction i with i is_lt, hinduction i, 
    { exact l_hd },
    { exact l_ih (fin.mk n (nat.lt_of_succ_lt_succ' is_lt)) } }
end

@[hott]
def tuple_of_list.map {A B : Type _} (f : A -> B) (l : list A) : 
  Π (i : fin (list.length l)), 
    tuple_of_list (list.map f l) (fin_size_eq (list_map_size_eq f l)⁻¹ i) = 
    f (tuple_of_list l i) :=
begin
  intro i, induction l, 
  { hinduction nat.not_lt_zero i.val i.is_lt },
  { hinduction i with i is_lt, hinduction i,
    { exact idp },
    { change tuple_of_list (list.map f l_tl) _ = f (tuple_of_list l_tl (fin.mk n _)), 
      rwr <- l_ih, apply ap (tuple_of_list (list.map f l_tl)), apply fin_eq, exact idp } }
end

@[hott, hsimp]
def tuple.append {A : Type _} {n m : ℕ} (B : tuple A n) (C : tuple A m) : 
  tuple A (n+m) :=
begin 
  intro i, hinduction nat.lt_sum_ge i.val n with in_sum p p,
  { exact B ⟨i.val, p⟩ },
  { exact C ⟨i.val-n, nat.sub_lt_of_lt_add i.is_lt p⟩ }
end 

@[hott]
def tuple.append_left {A : Type _} {n m : ℕ} (B : tuple A n) (C : tuple A m) :
  Π (i : fin n), tuple.append B C (fin_lift i) = B i :=
begin 
  intro i, 
  hinduction nat.lt_sum_ge (@fin_lift n m i).val n with in_sum q q, 
  { hsimp, rwr in_sum, apply ap B, apply fin_eq, exact idp }, 
  { hinduction nat.lt_irrefl _ (nat.lt_of_le_of_lt q i.is_lt) }
end  

@[hott]
def tuple.append_right {A : Type _} {n m : ℕ} (B : tuple A n) (C : tuple A m) :
  Π (i : fin m), tuple.append B C (fin_lift_rev i) = C i :=
begin 
  intro i, hinduction nat.lt_sum_ge (@fin_lift_rev n m i).val n with in_sum q q,
  { hinduction nat.not_lt_zero _ (nat.lt_of_add_lt_add_left q) },
  { hsimp, rwr in_sum, apply ap C, apply fin_eq, exact nat.add_sub_cancel_left' n i.val }
end

@[hott]
def fin_map_next {n : ℕ} (A : fin (n+1) -> Type _) :
  (Π (i : fin n), A (fin_lift i)) -> A ⟨n, nat.le_refl (n+1)⟩ -> 
  Π (i : fin (n+1)), A i :=
begin 
  intros fin_map a i, hinduction nat.eq_sum_lt_of_le (nat.le_of_succ_le_succ i.is_lt), 
  { have p : fin.mk n (nat.le_refl (n + 1)) = i, by fapply fin_eq; rwr val,
    rwr <- p, exact a },
  { have p : fin_lift (fin_desc i val) = i, by apply fin_lift_desc,
    rwr <- p, exact fin_map (fin_desc i val) }
end

@[hott, reducible]
def fin_map_two {A B : Type u} : A -> B -> Π (i : fin 2), tuple_of_list [A, B] i :=
begin
  intros a b i, hinduction i with i is_lt, hinduction i with i ih,
  { exact a },
  { hinduction i,
    { exact b },
    { change n + 2 < 2 + 0 at is_lt, rwr nat.add_comm n 2 at is_lt, 
      hinduction nat.not_lt_zero n (nat.lt_of_add_lt_add_left is_lt) } }
end

end hott