import hott.init hott.hit.trunc hott.types.trunc init2 nat2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat

namespace int

@[hott]
protected def coe_nat_eq (n : ℕ) : ↑n = int.of_nat n := rfl

@[hott]
def of_nat_zero : int.of_nat (0 : nat) = (0 : int) := rfl

@[hott]
def of_nat_one : int.of_nat (1 : nat) = (1 : int) := rfl

@[hott]
def sub_nat_nat (m n : ℕ) : ℤ :=
  dite (m ≥ n) (λ p, int.of_nat (m - n)) (λ np, -[1+ nat.pred (n - m)])

@[hott]
private def sub_nat_nat_of_lt {m n : ℕ} (h : m < n) : 
  int.sub_nat_nat m n = -[1+ nat.pred (n - m)] :=
have np : ¬(m ≥ n), from 
begin 
  hinduction nat.lt_sum_ge m n,
  { intro p, exact nat.lt_irrefl n (nat.lt_of_le_of_lt p h) },
  { intro p, exact nat.lt_irrefl n (nat.lt_of_le_of_lt p h) } 
end,
dif_neg np

@[hott]
private def sub_nat_nat_of_ge {m n : ℕ} (h : m ≥ n) : 
  int.sub_nat_nat m n = int.of_nat (m - n) :=
dif_pos h

@[hott]
def sub_nat_nat_self (m : ℕ) : sub_nat_nat m m = 0 :=
  by rwr sub_nat_nat_of_ge (nat.le_of_eq (@idp _ m)); rwr nat.sub_self' m

/- addition -/
@[hott]
protected def add : ℤ → ℤ → ℤ
| (int.of_nat m) (int.of_nat n) := int.of_nat (m + n)
| (int.of_nat m) -[1+ n]        := sub_nat_nat m (nat.succ n)
| -[1+ m]        (int.of_nat n) := sub_nat_nat n (nat.succ m)
| -[1+ m]        -[1+ n]        := -[1+ nat.succ (m + n)]

instance : has_add ℤ := ⟨int.add⟩

@[hott]
protected def add_comm : ∀ a b : ℤ, a + b = b + a
| (int.of_nat n) (int.of_nat m) := ap int.of_nat (nat.add_comm n m)
| (int.of_nat n) -[1+ m]        := rfl
| -[1+ n]        (int.of_nat m) := rfl
| -[1+ n]       -[1+m]          := ap (λ n, int.neg_succ_of_nat (nat.succ n)) 
                                      (nat.add_comm n m)

@[hott]
protected def add_zero : ∀ a : ℤ, a + 0 = a
| (int.of_nat n) := rfl
| -[1+ n]   := rfl

@[hott]
protected def zero_add (a : ℤ) : 0 + a = a :=
  int.add_comm 0 a ⬝ int.add_zero a

private def sub_nat_nat_add_add (m n k : ℕ) : 
  sub_nat_nat (m + k) (n + k) = sub_nat_nat m n :=
begin
  hinduction nat.lt_sum_ge m n with in_sum p p, 
  { have q : m + k < n + k, from nat.add_lt_add_right p k,
    rwr sub_nat_nat_of_lt q, rwr sub_nat_nat_of_lt p, rwr nat.add_sub_add_right' },
  { have q : m + k ≥ n + k, from nat.add_le_add_right p k,
    rwr sub_nat_nat_of_ge q, rwr sub_nat_nat_of_ge p, rwr nat.add_sub_add_right' }
end

@[hott]
private def sub_nat_nat_add (m n k : ℕ) : 
  int.sub_nat_nat (m + n) k = int.of_nat m + int.sub_nat_nat n k :=
begin
  apply @nat.lt_ge_by_cases (m + n) k, 
  { intro p, rwr sub_nat_nat_of_lt p, 
    have q : n < k, from nat.lt_of_le_of_lt (nat.le_add_left' n m) p,
    rwr sub_nat_nat_of_lt q, change _ = int.sub_nat_nat m _, 
    rwr succ_pred_of_pos' (nat.sub_gt_zero_of_lt q),
    have r : m < k - n, from nat.lt_sub_of_add_lt p,
    rwr sub_nat_nat_of_lt r, rwr nat.sub_sub', rwr nat.add_comm n m },
  { intro p, rwr sub_nat_nat_of_ge p, 
    apply @nat.lt_ge_by_cases n k,
    { intro q, rwr sub_nat_nat_of_lt q, 
      have r : m ≥ k - n, from 
      begin 
        apply @nat.le_of_add_le_add_left n, 
        rwr nat.add_sub_cancel_left'' _ _ (nat.le_of_lt q), rwr nat.add_comm, exact p 
      end, 
      calc int.of_nat (m + n - k) = int.of_nat (m - (k - n)) : 
                 ap int.of_nat (nat.add_sub_sub_sub r (nat.le_of_lt q))
           ... = int.sub_nat_nat m (k-n) : (sub_nat_nat_of_ge r)⁻¹
           ... = int.sub_nat_nat m (nat.succ (nat.pred (k-n))) : 
                 begin rwr succ_pred_of_pos' (nat.sub_gt_zero_of_lt q) end
           ... = int.of_nat m + -[1+ nat.pred (k - n)] : idp },
    { intro q, rwr sub_nat_nat_of_ge q, apply ap int.of_nat, 
      exact nat.add_sub_assoc q m } }
end

@[hott]
def sub_nat_nat_sub (m : ℕ) {n k : ℕ} (H : k ≥ n) :
  sub_nat_nat (m + n) k = sub_nat_nat m (k - n) :=
begin
  rwr <- nat.add_sub_cancel_left'' n k H, rwr nat.add_comm n (k - n),
  rwr sub_nat_nat_add_add _ _ n, rwr nat.add_sub_cancel' _ n
end

@[hott]
private def sub_nat_nat_add_neg_succ_of_nat (m n k : ℕ) :
    sub_nat_nat m n + -[1+ k] = sub_nat_nat m (n + nat.succ k) :=
begin
  hinduction nat.lt_sum_ge m n with in_sum p p,
  { have q : m < n + (k + 1), from nat.lt_add_of_lt_right' p _,
    rwr sub_nat_nat_of_lt p, rwr sub_nat_nat_of_lt q, change -[1+ _] = _,
    rwr <- nat.add_succ, rwr nat.add_sub_comm _ _ _ (nat.le_of_lt p), 
    rwr nat.pred_add_pred_add_pos (nat.sub_gt_zero_of_lt p) },
  { rwr sub_nat_nat_of_ge p, change sub_nat_nat _ _ = _, 
    rwr <- sub_nat_nat_add_add _ _ n, rwr <- nat.add_sub_comm _ _ _ p, 
    rwr nat.add_sub_cancel', rwr nat.add_comm }
end

@[hott]
private def add_assoc_aux1 (m n : ℕ) :
    Π c : ℤ, int.of_nat m + int.of_nat n + c = int.of_nat m + (int.of_nat n + c)
| (int.of_nat k) := ap int.of_nat (nat.add_assoc m n k)
| -[1+ k]        := 
    begin 
      change int.sub_nat_nat (m + n) (nat.succ k) = _ + int.sub_nat_nat n (nat.succ k),
      exact sub_nat_nat_add _ _ _ 
    end

@[hott]
private def add_assoc_aux2 (m n k : ℕ) :
  -[1+ m] + -[1+ n] + int.of_nat k = -[1+ m] + (-[1+ n] + int.of_nat k) :=
begin
  change sub_nat_nat k _ = _ + sub_nat_nat _ _, rwr int.add_comm -[1+ m],
  rwr sub_nat_nat_add_neg_succ_of_nat, rwr nat.add_succ _ m, rwr nat.succ_add n,
  rwr nat.add_comm n m
end

@[hott]
protected def add_assoc : ∀ a b c : ℤ, a + b + c = a + (b + c)
| (int.of_nat m) (int.of_nat n) c              := add_assoc_aux1 _ _ _
| (int.of_nat m) b              (int.of_nat k) := 
    by rwr int.add_comm; rwr <- add_assoc_aux1; rwr int.add_comm (int.of_nat k);
       rwr add_assoc_aux1; rwr int.add_comm b  
| a              (int.of_nat n) (int.of_nat k) := 
    by rwr int.add_comm; rwr int.add_comm a; rwr ← add_assoc_aux1; rwr int.add_comm a;
       rwr int.add_comm (int.of_nat k)
| -[1+ m]        -[1+ n]        (int.of_nat k) := add_assoc_aux2 _ _ _
| -[1+ m]        (int.of_nat n) -[1+ k]        := 
    by rwr int.add_comm; rwr ← add_assoc_aux2; rwr int.add_comm (int.of_nat n);
       rwr ← add_assoc_aux2; rwr int.add_comm -[1+ m]
| (int.of_nat m) -[1+ n]        -[1+ k]        := 
    by rwr int.add_comm; rwr int.add_comm (int.of_nat m); rwr int.add_comm (int.of_nat m); 
       rwr ← add_assoc_aux2; rwr int.add_comm -[1+ k]
| -[1+ m]        -[1+ n]        -[1+ k]        := 
    by change -[1+ _] = -[1+ _]; rwr nat.add_succ; rwr nat.succ_add _ k; 
       rwr nat.add_assoc m n k

/- negative -/
@[hott]
protected def add_left_neg : ∀ a : ℤ, -a + a = 0
| (int.of_nat 0)            := rfl
| (int.of_nat (nat.succ m)) := sub_nat_nat_self _
| -[1+ m]                   := sub_nat_nat_self _
    
/- multiplication -/
@[hott]
protected def mul_comm : ∀ a b : ℤ, a * b = b * a
| (int.of_nat m) (int.of_nat n) := 
    by change int.of_nat _ = int.of_nat _; rwr nat.mul_comm
| (int.of_nat m) -[1+ n]        := 
    by change int.neg_of_nat _ = int.neg_of_nat _; rwr nat.mul_comm
| -[1+ m]        (int.of_nat n) := 
    by change int.neg_of_nat _ = int.neg_of_nat _; rwr nat.mul_comm
| -[1+ m]        -[1+ n]        := 
    by change int.of_nat _ = int.of_nat _; rwr nat.mul_comm

@[hott]
protected def mul_one : ∀ (a : ℤ), a * 1 = a
| (int.of_nat m) := by change int.of_nat (_ * _) = _; rwr nat.mul_one
| -[1+ m]        := by change int.neg_of_nat (_ * _) = _; rwr nat.mul_one

@[hott]
protected def one_mul (a : ℤ) : 1 * a = a :=
  by rwr int.mul_comm; exact int.mul_one _

@[hott]
protected def mul_zero : ∀ (a : ℤ), a * 0 = 0
| (int.of_nat m) := rfl
| -[1+ m]    := rfl

@[hott]
protected def zero_mul (a : ℤ) : 0 * a = 0 :=
  by rwr int.mul_comm 0 a; exact int.mul_zero a

@[hott]
private def of_nat_mul_neg_of_nat (m : ℕ) :
   ∀ n, int.of_nat m * int.neg_of_nat n = int.neg_of_nat (m * n)
| 0            := rfl
| (nat.succ n) := idp 

@[hott]
private def neg_of_nat_mul_of_nat (m n : ℕ) :
    int.neg_of_nat m * int.of_nat n = int.neg_of_nat (m * n) :=
by rwr int.mul_comm; rwr of_nat_mul_neg_of_nat; rwr nat.mul_comm

@[hott]
private def neg_succ_of_nat_mul_neg_of_nat (m : ℕ) :
  ∀ n, -[1+ m] * int.neg_of_nat n = int.of_nat (nat.succ m * n)
| 0            := rfl
| (nat.succ n) := idp

@[hott]
private def neg_of_nat_mul_neg_succ_of_nat (m n : ℕ) :
  int.neg_of_nat n * -[1+ m] = int.of_nat (n * nat.succ m) :=
by rwr int.mul_comm; rwr neg_succ_of_nat_mul_neg_of_nat; rwr nat.mul_comm

@[hott]
protected def mul_assoc : ∀ a b c : ℤ, a * b * c = a * (b * c)
| (int.of_nat m) (int.of_nat n) (int.of_nat k) := 
    by change int.of_nat _ = int.of_nat _; rwr nat.mul_assoc
| (int.of_nat m) (int.of_nat n) -[1+ k]        := 
    by change int.neg_of_nat _ = _ * int.neg_of_nat _; rwr of_nat_mul_neg_of_nat;
       rwr nat.mul_assoc
| (int.of_nat m) -[1+ n]        (int.of_nat k) := 
    by change int.neg_of_nat _ * _ = _ * int.neg_of_nat _; rwr of_nat_mul_neg_of_nat;
       rwr neg_of_nat_mul_of_nat; rwr nat.mul_assoc
| (int.of_nat m) -[1+ n]        -[1+ k]        := 
    by change int.neg_of_nat _ * _ = int.of_nat _; rwr neg_of_nat_mul_neg_succ_of_nat;
       rwr nat.mul_assoc
| -[1+ m]        (int.of_nat n) (int.of_nat k) := 
    by change int.neg_of_nat _ * _ = int.neg_of_nat _; rwr neg_of_nat_mul_of_nat;
       rwr nat.mul_assoc
| -[1+ m]        (int.of_nat n) -[1+ k]        := 
    by change int.neg_of_nat _ * _ = _ * int.neg_of_nat _; 
       rwr neg_of_nat_mul_neg_succ_of_nat; rwr neg_succ_of_nat_mul_neg_of_nat; 
       rwr nat.mul_assoc
| -[1+ m]        -[1+ n]        (int.of_nat k) := 
    by change int.of_nat _ = _ * int.neg_of_nat _; 
       rwr neg_succ_of_nat_mul_neg_of_nat; rwr nat.mul_assoc
| -[1+ m]        -[1+ n]        -[1+ k]        := 
    by change int.neg_of_nat _ = int.neg_of_nat _; rwr nat.mul_assoc

@[hott]
private def neg_of_nat_eq_sub_nat_nat_zero : ∀ n, int.neg_of_nat n = sub_nat_nat 0 n
| 0        := rfl
| (nat.succ n) := rfl

@[hott]
private def neg_of_nat_add (m n : ℕ) :
  int.neg_of_nat m + int.neg_of_nat n = int.neg_of_nat (m + n) :=
begin
  hinduction m with m ih,
  { change (0 : ℤ) + _ = _, rwr int.zero_add, rwr nat.zero_add },
  { hinduction n with n ih', 
    { exact idp },
    { rwr neg_of_nat_eq_sub_nat_nat_zero, rwr neg_of_nat_eq_sub_nat_nat_zero,
      rwr neg_of_nat_eq_sub_nat_nat_zero, rwr sub_nat_nat_of_lt (nat.zero_lt_succ _), 
      rwr sub_nat_nat_of_lt (nat.zero_lt_succ _), change _ = sub_nat_nat 0 (nat.succ _),
      rwr sub_nat_nat_of_lt (nat.zero_lt_succ _), rwr nat.sub_zero', 
      rwr nat.sub_zero', rwr nat.sub_zero', 
      change -[1+ m] + -[1+ n] = -[1+ (nat.succ m) + n], rwr nat.succ_add } }
end

/- Distributivity -/
@[hott]
private def of_nat_mul_sub_nat_nat (m n k : ℕ) :
  int.of_nat m * sub_nat_nat n k = sub_nat_nat (m * n) (m * k) :=
begin
  hinduction nat.eq_sum_lt_of_le (nat.zero_le m) with in_sum p p,
  { rwr <- p, change (0 : int) * _ = _, 
    rwr int.zero_mul, rwr nat.zero_mul, rwr nat.zero_mul },
  { hinduction nat.lt_sum_ge n k with in_sum' q q,
    { rwr sub_nat_nat_of_lt q, rwr sub_nat_nat_of_lt (nat.mul_lt_mul_of_pos_left q p),
      change int.neg_of_nat _ = int.neg_of_nat (nat.succ _), apply ap int.neg_of_nat,
      rwr succ_pred_of_pos' (nat.sub_gt_zero_of_lt q),
      rwr succ_pred_of_pos' (nat.sub_gt_zero_of_lt (nat.mul_lt_mul_of_pos_left q p)),
      exact nat.mul_sub_left_distrib' _ _ _ },
    { rwr sub_nat_nat_of_ge q, rwr sub_nat_nat_of_ge (nat.mul_le_mul_left m q),
      apply ap int.of_nat, exact nat.mul_sub_left_distrib' _ _ _ } }
end

@[hott]
private def neg_succ_of_nat_mul_sub_nat_nat (m n k : ℕ) :
  -[1+ m] * sub_nat_nat n k = sub_nat_nat (nat.succ m * k) (nat.succ m * n) :=
begin
  hinduction nat.lt_sum_ge n k with in_sum' q q,
  { rwr sub_nat_nat_of_lt q, 
    rwr sub_nat_nat_of_ge (nat.mul_le_mul_left (nat.succ m) (nat.le_of_lt q)),
    change int.of_nat _ = _, apply ap int.of_nat, 
    rwr succ_pred_of_pos' (nat.sub_gt_zero_of_lt q), exact nat.mul_sub_left_distrib' _ _ _ },
  { rwr sub_nat_nat_of_ge q, change int.neg_of_nat _ = _, 
    rwr <- nat.zero_add (nat.succ m * k), 
    rwr sub_nat_nat_sub 0 (nat.mul_le_mul_left (nat.succ m) q),
    rwr neg_of_nat_eq_sub_nat_nat_zero, apply ap (sub_nat_nat 0), 
    exact nat.mul_sub_left_distrib' _ _ _ }
end

@[hott]
protected def distrib_left : ∀ a b c : ℤ, a * (b + c) = a * b + a * c
| (int.of_nat m) (int.of_nat n) (int.of_nat k) := 
    by change int.of_nat _ = int.of_nat _; rwr nat.left_distrib
| (int.of_nat m) (int.of_nat n) -[1+ k]        := 
    by change _ * sub_nat_nat _ _ = _; rwr of_nat_mul_sub_nat_nat; 
       rwr <- nat.add_zero (m * n); rwr sub_nat_nat_add (m * n);
       rwr <- neg_of_nat_eq_sub_nat_nat_zero; exact idp
| (int.of_nat m) -[1+ n]        (int.of_nat k) := 
    by change _ * sub_nat_nat _ _ = _; rwr of_nat_mul_sub_nat_nat; 
       rwr <- nat.add_zero (m * k); rwr sub_nat_nat_add (m * k);
       rwr <- neg_of_nat_eq_sub_nat_nat_zero; rwr int.add_comm (int.of_nat (m * k));
       exact idp
| (int.of_nat m) -[1+ n]        -[1+ k]        := 
    begin change int.neg_of_nat _ = _, rwr <- nat.add_succ n k, rwr <- nat.succ_add n,
          rwr nat.left_distrib, rwr <- neg_of_nat_add end
| -[1+ m]        (int.of_nat n) (int.of_nat k) := 
    by change int.neg_of_nat (_ * _) = _; rwr nat.left_distrib; rwr <- neg_of_nat_add
| -[1+ m]        (int.of_nat n) -[1+ k]        := 
    begin change _ * sub_nat_nat _ _ = _, rwr neg_succ_of_nat_mul_sub_nat_nat,
          rwr <- nat.add_zero ((m+1) * (k+1)), rwr sub_nat_nat_add, 
          rwr <- neg_of_nat_eq_sub_nat_nat_zero, rwr int.add_comm end
| -[1+ m]        -[1+ n]        (int.of_nat k) :=
    begin change _ * sub_nat_nat _ _ = _, rwr neg_succ_of_nat_mul_sub_nat_nat,
          rwr <- nat.add_zero ((m+1) * (n+1)), rwr sub_nat_nat_add, 
          rwr <- neg_of_nat_eq_sub_nat_nat_zero end
| -[1+ m]        -[1+ n]        -[1+ k]        := 
    begin change int.of_nat _ = int.of_nat _, rwr <- nat.add_succ n k, 
          rwr <- nat.succ_add n, rwr nat.left_distrib end

@[hott]
protected def distrib_right (a b c : ℤ) : (a + b) * c = a * c + b * c :=
  by rwr int.mul_comm; rwr int.mul_comm a; rwr int.mul_comm b; exact int.distrib_left _ _ _

end int

end hott
