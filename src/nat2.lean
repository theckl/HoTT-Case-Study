import hott.init hott.hit.trunc hott.types.trunc hott.types.nat.order init2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat

/- Facts about natural numbers not found in the [HoTT3]-library (or only as theorems). -/
open nat

@[hott] 
def eq_zero_sum_eq_succ_pred (n : ℕ) : n = 0 ⊎ n = succ (pred n) :=
begin
  hinduction n with n IH,
  { exact sum.inl rfl },
  { exact sum.inr rfl }
end

@[hott] 
def exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : Σk : ℕ, n = succ k :=
  sigma.mk (pred n) (sum.resolve_left (eq_zero_sum_eq_succ_pred n) H)

@[hott, elab_as_eliminator] 
def nat.sub_induction' {P : ℕ → ℕ → Type _} (n m : ℕ) (H1 : Πm, P 0 m)
   (H2 : Πn, P (succ n) 0) (H3 : Πn m, P n m → P (succ n) (succ m)) : P n m :=
have general : Πm, P n m, from nat.rec_on n H1
  (λk : ℕ,
    assume IH : Πm, P k m,
    λm : ℕ,
    nat.cases_on m (H2 k) (λl, (H3 k l (IH l)))),
general m

@[hott, hsimp] 
def nat.succ_sub_succ_eq_sub' (a b : ℕ) : succ a - succ b = a - b :=
nat.rec (by hsimp) (λ b, ap pred) b

@[hott] 
def nat.sub_zero' (n : ℕ) : n - 0 = n := rfl

@[hott] 
def nat.sub_succ' (n m : ℕ) : n - succ m = pred (n - m) := rfl

@[hott] 
def nat.sub_sub' (n m k : nat) : n - m - k = n - (m + k) :=
nat.rec_on k
  (calc
    n - m - 0 = n - m        : by rwr nat.sub_zero'
          ... = n - (m + 0)  : by rwr nat.add_zero)
  (λl : nat,
    assume IH : n - m - l = n - (m + l),
    calc
      n - m - succ l = pred (n - m - l)   : by rwr nat.sub_succ'
                 ... = pred (n - (m + l)) : by rwr IH
                 ... = n - succ (m + l)   : by rwr nat.sub_succ'
                 ... = n - (m + succ l)   : by rwr add_succ)


@[hott] 
def nat.zero_sub' (n : ℕ) : 0 - n = 0 :=
nat.rec_on n (nat.sub_zero' _)
  (λk : nat,
    assume IH : 0 - k = 0,
    calc
      0 - succ k = pred (0 - k) : by rwr nat.sub_succ'
             ... = pred 0       : by rwr IH
             ... = 0            : pred_zero)

@[hott] 
def nat.succ_sub_succ' (n m : ℕ) : succ n - succ m = n - m :=
  nat.succ_sub_succ_eq_sub' n m

@[hott] 
def nat.sub_self' (n : ℕ) : n - n = 0 :=
nat.rec_on n (nat.sub_zero' _) (λk IH, nat.succ_sub_succ' _ _ ⬝ IH)

@[hott] 
def nat.sub_self_add' (n m : ℕ) : n - (n + m) = 0 :=
calc
  n - (n + m) = n - n - m : by rwr nat.sub_sub'
          ... = 0 - m     : by rwr nat.sub_self'
          ... = 0         : by rwr nat.zero_sub'

@[hott] 
def nat.sub_eq_zero_of_le {n m : ℕ} (H : n ≤ m) : n - m = 0 :=
   begin hinduction le.elim H with p k Hk, rwr <- Hk, apply nat.sub_self_add' end

@[hott] 
def nat.add_sub_assoc {m k : ℕ} (H : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
  have l1 : k ≤ m → n + m - k = n + (m - k), from
    nat.sub_induction' k m
    (λm : ℕ, assume H : 0 ≤ m,
       calc
         n + m - 0 = n + m       : by rwr nat.sub_zero'
               ... = n + (m - 0) : by rwr nat.sub_zero')
     (λk : ℕ, assume H : succ k ≤ 0, absurd H (not_succ_le_zero _))
     (λk m,
       assume IH : k ≤ m → n + m - k = n + (m - k),
       λH : succ k ≤ succ m,
       calc
         n + succ m - succ k = succ (n + m) - succ k : by rwr add_succ
                         ... = n + m - k             : by rwr nat.succ_sub_succ'
                         ... = n + (m - k)           : IH (le_of_succ_le_succ H)
                         ... = n + (succ m - succ k) : by rwr nat.succ_sub_succ'),
 l1 H

@[hott] 
def nat.sub_le_sub_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n - k ≤ m - k :=
begin  
  let l := (le.elim H).1, let Hl := (le.elim H).2,
  apply sum.elim (@nat.le_total n k),
  { intro H2, rwr nat.sub_eq_zero_of_le H2, exact nat.zero_le (m - k) },
  { intro H2,
    have H3 : n - k + l = m - k, from
      calc n - k + l = l + (n - k) : by rwr nat.add_comm
                 ... = l + n - k   : by rwr <- nat.add_sub_assoc H2 l
                 ... = n + l - k   : by rwr nat.add_comm
                 ... = m - k       : by rwr Hl,
    exact le.intro H3}
end

@[hott] def nat.succ_sub {m n : ℕ} : m ≥ n → succ m - n  = succ (m - n) :=
  nat.sub_induction' n m (λk, assume H : 0 ≤ k, rfl)
    (λk,
     assume H : succ k ≤ 0,
     absurd H (not_succ_le_zero _))
   (λk l,
     assume IH : k ≤ l → succ l - k = succ (l - k),
     λH : succ k ≤ succ l,
     calc
       succ (succ l) - succ k = succ l - k             : by rwr nat.succ_sub_succ'
                          ... = succ (l - k)           : IH (le_of_succ_le_succ H)
                          ... = succ (succ l - succ k) : by rwr nat.succ_sub_succ')

@[hott] 
def nat.add_sub_cancel' (n m : ℕ) : n + m - m = n :=
nat.rec_on m
  (begin rwr hott.algebra.add_zero end)
  (λk : ℕ,
    assume IH : n + k - k = n,
    calc
      n + succ k - succ k = succ (n + k) - succ k : by rwr add_succ
                      ... = n + k - k             : by rwr nat.succ_sub_succ'
                      ... = n                     : IH)

@[hott] 
def nat.add_sub_cancel_left' (n m : ℕ) : n + m - n = m :=
by rwr nat.add_comm; apply nat.add_sub_cancel'

@[hott] 
def nat.add_sub_cancel_left'' (n m : ℕ) : n ≤ m -> n + (m - n) = m :=
begin 
  intro p, let k := (le.elim p).1, let q := (le.elim p).2, rwr <- q, 
  rwr nat.add_sub_cancel_left' 
end

@[hott]
def nat.sub_lt_of_lt_add {v n m : nat} (h₁ : v < n + m) (h₂ : v ≥ n) : v - n < m :=
  have nat.succ v ≤ n + m,   from succ_le_of_lt h₁,
  have nat.succ (v - n) ≤ m, from
    calc nat.succ (v - n) = nat.succ v - n : by rwr <- nat.succ_sub h₂
                  ...     ≤ n + m - n      : nat.sub_le_sub_right this n
                  ...     = m              : nat.add_sub_cancel_left' n m,
lt_of_succ_le this

@[hott]
def nat.lt_of_le_neq {m n : nat} (h₁: m ≤ n) (h₂ : m ≠ n) : m < n :=
  begin hinduction nat.eq_sum_lt_of_le h₁, hinduction h₂ val, exact val end

@[hott] 
def nat.eq_zero_of_le_zero' {n : ℕ} (H : n ≤ 0) : n = 0 :=
  begin hinduction n, exact idp, hinduction nat.not_succ_le_zero n H end

end hott