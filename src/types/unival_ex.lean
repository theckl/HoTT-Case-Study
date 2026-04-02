import init2

universes u v w
hott_theory

namespace hott
open hott.is_equiv

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
| (nat.succ n) bin  := double_binℕ (doubles_binℕ n bin)

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
| (nat.succ m) := succ_binℕ (nat_to_binℕ m)

/- To show that the conversion functions are inverse to each other, we first need to 
   verify that they respect the successor and the double function. -/
@[hott]
def succ_ℕ_binℕ (n : nat) : nat_to_binℕ (nat.succ n) = succ_binℕ (nat_to_binℕ n) :=
  idp 

@[hott]
def succ_binℕ_ℕ (n : binℕ) : binℕ_to_nat (succ_binℕ n) = nat.succ (binℕ_to_nat n) :=
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
  { change nat_to_binℕ (nat.succ (nat.succ (2 * n))) = _, 
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
| (nat.succ m) n := 2 * doubles_ℕ m n

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

end hott