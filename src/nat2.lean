import hott.init hott.hit.trunc hott.types.trunc hott.types.nat.order init2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat unit

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

/- We formalize the example on the use of (computational) univalence presented in the 
   paper [Vezzosi, Abel and Mörtberg: Cubical Agda]: When calculating 
   with natural numbers, the unary representation `nat` is good for proofs of laws, but
   the binary representation `binnat` defined below is effective for actual calculations. 
   Univalence can be used to transport the results forth and backwards between the two 
   representations, thus minimizing the necessary efforts. We exemplify this strategy on
   a calculation on powers of 2.
   
   First, we define binary natural numbers. We need to distinguish zero and positive 
   binary numbers. -/
@[hott]
inductive posbinℕ 
| pos1 : posbinℕ
| x0 (pos : posbinℕ) : posbinℕ
| x1 (pos : posbinℕ) : posbinℕ

@[hott]
inductive binℕ
| bin0 : binℕ 
| binpos (pos : posbinℕ) : binℕ

/- Next, we introduce the successor, double and iterated double (= power to basis 2) 
   functions on binary natural numbers. -/
@[hott]
def succ_posbinℕ : posbinℕ -> posbinℕ
| posbinℕ.pos1     := posbinℕ.x0 posbinℕ.pos1 
| (posbinℕ.x0 pos) := posbinℕ.x1 pos
| (posbinℕ.x1 pos) := posbinℕ.x0 (succ_posbinℕ pos)

@[hott]
def succ_binℕ : binℕ -> binℕ
| binℕ.bin0         := binℕ.binpos posbinℕ.pos1 
| (binℕ.binpos pos) := binℕ.binpos (succ_posbinℕ pos)

@[hott]
def double_binℕ : binℕ -> binℕ
| binℕ.bin0         := binℕ.bin0 
| (binℕ.binpos pos) := binℕ.binpos (posbinℕ.x0 pos)

@[hott]
def doubles_binℕ : nat -> binℕ -> binℕ
| 0        bin  := bin 
| (succ n) bin  := double_binℕ (doubles_binℕ n bin)

/- We need an equality for doubling and successors of binary numbers. -/
@[hott]
def double_succ_binℕ (n : binℕ) : 
  double_binℕ (succ_binℕ n) = succ_binℕ (succ_binℕ (double_binℕ n)) :=
begin
  hinduction n, 
  { exact idp },
  { exact idp }
end 

/- The conversion functions from binary to natural numbers and back. -/
@[hott]
def posbinℕ_to_nat : posbinℕ -> nat
| posbinℕ.pos1     := 1 
| (posbinℕ.x0 pos) := 2 * (posbinℕ_to_nat pos)
| (posbinℕ.x1 pos) := 2 * (posbinℕ_to_nat pos) + 1

@[hott]
def binℕ_to_nat : binℕ -> nat
| binℕ.bin0         := 0 
| (binℕ.binpos pos) := posbinℕ_to_nat pos

@[hott]
def nat_to_binℕ : nat -> binℕ 
| 0        := binℕ.bin0 
| (succ m) := succ_binℕ (nat_to_binℕ m)

/- To show that the conversion functions are inverse to each other, we first need to 
   verify that they respect the successor and the double function. -/
@[hott]
def succ_ℕ_binℕ (n : nat) : nat_to_binℕ (succ n) = succ_binℕ (nat_to_binℕ n) :=
  idp 

@[hott]
def succ_binℕ_ℕ (n : binℕ) : binℕ_to_nat (succ_binℕ n) = succ (binℕ_to_nat n) :=
begin  
  hinduction n, 
  { exact idp },
  { change posbinℕ_to_nat (succ_posbinℕ pos) = _, hinduction pos, 
    { exact idp },
    { exact idp },
    { change 2 * _ = _, rwr ih } }
end 

@[hott]
def double_ℕ_binℕ (n : nat) : nat_to_binℕ (2 * n) = double_binℕ (nat_to_binℕ n) :=
begin
  hinduction n,
  { exact idp },
  { change nat_to_binℕ (succ (succ (2 * n))) = _, 
    rwr succ_ℕ_binℕ, rwr succ_ℕ_binℕ, rwr succ_ℕ_binℕ, rwr ih, rwr double_succ_binℕ }
end 

/- Now we can prove that the conversion functions are inverse to each other. -/
@[hott]
def nat_binℕ.right_inv (n : binℕ) : nat_to_binℕ (binℕ_to_nat n) = n := 
begin 
  hinduction n, 
  { exact idp }, 
  { hinduction pos, 
    { exact idp },
    { change nat_to_binℕ (2 * (posbinℕ_to_nat pos)) = _, rwr double_ℕ_binℕ, 
      change nat_to_binℕ (posbinℕ_to_nat pos) = _ at ih, rwr ih },
    { change nat_to_binℕ (2 * (posbinℕ_to_nat pos) + 1) = _, rwr succ_ℕ_binℕ, 
      rwr double_ℕ_binℕ, change nat_to_binℕ (posbinℕ_to_nat pos) = _ at ih, rwr ih } }
end

@[hott]
def nat_binℕ.left_inv (n : nat) : binℕ_to_nat (nat_to_binℕ n) = n := 
begin
  hinduction n, 
  { exact idp },
  { rwr succ_ℕ_binℕ, rwr succ_binℕ_ℕ, rwr ih }   
end

/- The conversion functions and their inverseness gives rise to equivalence and hence to
   equalities, by univalence. -/
@[hott]
def ℕ_equiv_binℕ : nat ≃ binℕ :=
  equiv.mk nat_to_binℕ (adjointify _ binℕ_to_nat nat_binℕ.right_inv nat_binℕ.left_inv)

@[hott]
def binℕ_equiv_ℕ : binℕ  ≃ nat := equiv.symm ℕ_equiv_binℕ

@[hott]
def ℕ_eq_binℕ : nat = binℕ := ua ℕ_equiv_binℕ

@[hott]
def ℕ_to_binℕ_tr_fn : Π (n : nat), ℕ_eq_binℕ ▸[λ B, B] n = nat_to_binℕ n :=
  λ n, cast_ua ℕ_equiv_binℕ n

@[hott]
def binℕ_eq_ℕ : binℕ = nat := ua binℕ_equiv_ℕ

@[hott]
def binℕ_eq_ℕ_inv : binℕ_eq_ℕ = ℕ_eq_binℕ⁻¹ := 
  begin change ua (equiv.symm ℕ_equiv_binℕ) = eq.inverse (ua _), rwr equiv.ua_symm end

@[hott]
def binℕ_to_ℕ_tr_fn : Π (n : binℕ), binℕ_eq_ℕ ▸[λ B, B] n = binℕ_to_nat n :=
  λ n, cast_ua binℕ_equiv_ℕ n

/- Now we show an equality involving powers of 2 in the type `nat`. The tactics `refl` 
   leads to a deterministic timeout on my machine, whereas the binary calculation is 
   terminating. 
   
   We first define the unary version of `doubles` and show that it transports to
   `doubles_binℕ`. -/
@[hott]
def doubles_ℕ : nat -> nat -> nat
| 0        n := n 
| (succ m) n := 2 * doubles_ℕ m n

@[hott]
def doubles_ℕ_to_binℕ (n : nat) : 
  ℕ_eq_binℕ ▸[λ B, B -> B] (doubles_ℕ n) = doubles_binℕ n :=
begin
  fapply eq_of_homotopy, intro k, 
  rwr tr_endo_eval_tr_endo_tr, rwr ℕ_to_binℕ_tr_fn, rwr <- binℕ_eq_ℕ_inv, 
  rwr binℕ_to_ℕ_tr_fn, 
  hinduction n,
  { change nat_to_binℕ (binℕ_to_nat k) = k, exact nat_binℕ.right_inv k },
  { change nat_to_binℕ (2 * _) = double_binℕ _, rwr double_ℕ_binℕ, rwr ih }
end 

/- Finally, we can calculate the equality of powers of 2.

   Note: The transport over the equality `ℕ = binℕ` does not compute, neither on natural
   numbers nor on functions of natural numbers, so we have to perform the transports 
   manually.  -/
@[hott]  --[GEVE]
def power_of_2_eq : doubles_ℕ 20 1024 = doubles_ℕ 5 (doubles_ℕ 15 1024) :=
begin
  fapply @tr_eq_tr_to_eq _ _ _ ℕ_eq_binℕ (λ B, B), 
  rwr @tr_endo_eval_tr_tr _ _ _ ℕ_eq_binℕ (λ B, B) (doubles_ℕ 20),
  rwr @tr_endo_eval_tr_tr _ _ _ ℕ_eq_binℕ (λ B, B) (doubles_ℕ 5),
  rwr @tr_endo_eval_tr_tr _ _ _ ℕ_eq_binℕ (λ B, B) (doubles_ℕ 15),
  rwr ℕ_to_binℕ_tr_fn, 
  rwr doubles_ℕ_to_binℕ, rwr doubles_ℕ_to_binℕ, rwr doubles_ℕ_to_binℕ
end

/- Facts on iterations of functions -/
@[hott]
def fn_eq_iterate {N M : Type _} {f : N -> M} (hN : N -> N) {g : M -> N} 
  (rinv : Π (m : M), f (g m) = m) (linv : Π (n : N), g (f n) = n) (s : ℕ) : 
  Π (m : M), (f ∘ hN ∘ g)^[s] m = f (hN^[s] (g m)) :=
begin 
  intro m, hinduction s,
  { exact (rinv m)⁻¹ },
  { change f (hN (g _)) = f (hN _), rwr ih, rwr linv } 
end

@[hott]
def nth_iter_eq_n : Π (n : ℕ), succ^[n] 0 = n :=
begin intro n, hinduction n, exact idp, apply ap nat.succ, assumption end 

end hott