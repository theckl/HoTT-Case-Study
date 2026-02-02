import sets.basic

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv hott.is_equiv nat 

namespace set

/- Natural numbers form a set. We need the encode-decode method. -/
@[hott, reducible]
def nat_code : ℕ -> ℕ -> Type _
| 0     0     := One 
| (n+1) 0     := Zero
| 0     (m+1) := Zero
| (n+1) (m+1) := nat_code n m

@[hott, instance]
def nat_code_is_prop : Π (n m : ℕ), is_prop (nat_code n m)
| 0     0     := by change is_prop One; apply_instance 
| (n+1) 0     := by change is_prop Zero; apply_instance
| 0     (m+1) := by change is_prop Zero; apply_instance
| (n+1) (m+1) := by change is_prop (nat_code n m); exact nat_code_is_prop n m
 
@[hott]
def nat_refl : Π (n : ℕ), nat_code n n :=
  begin intro n, hinduction n, exact One.star, exact ih end 

@[hott]
def nat_decode : Π (n m : ℕ), nat_code n m -> n = m
| 0     0     := λ cd, idp  
| (n+1) 0     := λ cd, by hinduction cd
| 0     (m+1) := λ cd, by hinduction cd
| (n+1) (m+1) := λ cd, ap nat.succ (nat_decode n m cd)

@[hott, instance]  --[GEVE]
def nat_is_set : is_set ℕ :=
begin 
  fapply @encode_decode_set _ nat_code nat_refl nat_code_is_prop, 
  intros a b cd, exact nat_decode _ _ cd 
end

@[hott]
def nat_Set : Set :=
  Set.mk ℕ nat_is_set

/- Equality in the set of natural numbers is decidable. -/
@[hott]
def dec_nat : dec_Set := @dec_Set.mk nat_Set nat_eq_is_decidable 


/- integers form a set. We use the encode-decode method for ℕ. -/
@[hott]
def int_code : ℤ -> ℤ -> Type _
| (int.of_nat n) (int.of_nat m) := nat_code n m
| (int.of_nat n) -[1+ m]        := Zero
| -[1+ n]        (int.of_nat m) := Zero
| -[1+ n]        -[1+m]         := nat_code n m

@[hott, instance]
def int_code_is_prop : Π (n m : ℤ), is_prop (int_code n m)
| (int.of_nat n) (int.of_nat m) := by exact nat_code_is_prop n m
| (int.of_nat n) -[1+ m]        := by change is_prop Zero; apply_instance
| -[1+ n]        (int.of_nat m) := by change is_prop Zero; apply_instance
| -[1+ n]        -[1+m]         := by exact nat_code_is_prop n m

@[hott]
def int_refl : Π (n : ℤ), int_code n n
| (int.of_nat n) := nat_refl n
| -[1+ n]        := nat_refl n 

@[hott]
def int_decode : Π (n m : ℤ), int_code n m -> n = m
| (int.of_nat n) (int.of_nat m) := λ c, ap int.of_nat (nat_decode n m c)
| (int.of_nat n) -[1+ m]        := λ c, by hinduction c
| -[1+ n]        (int.of_nat m) := λ c, by hinduction c 
| -[1+ n]        -[1+m]         := λ c, ap int.neg_succ_of_nat (nat_decode n m c)

@[hott, instance] 
def int_is_set : is_set ℤ :=
begin 
  fapply @encode_decode_set _ int_code int_refl int_code_is_prop, 
  intros a b cd, exact int_decode _ _ cd 
end

@[hott]
def int_Set : Set :=
  Set.mk ℤ int_is_set 

/- Finite sets are sets. -/
@[hott]
def fin_eqv_sigma (n : nat) : fin n ≃ Σ (m : ℕ), m < n :=
begin
  fapply equiv.mk,
  { intro m, hinduction m with m is_lt, exact ⟨m, is_lt⟩ },
  { fapply adjointify,
    { intro m, hinduction m with m is_lt, exact fin.mk m is_lt },
    { intro m, hinduction m with m is_lt, exact idp },
    { intro m, hinduction m with m is_lt, exact idp } }
end


@[hott, instance]
def fin_is_set (n : nat) : is_set (fin n) :=
begin
  apply is_trunc_equiv_closed_rev 0 (fin_eqv_sigma n), 
  fapply dprod_of_Sets_is_set'
end

/- Lists of elements in a set form a set. -/
@[hott]
def list_code {A : Set.{u}} : list A -> list A -> Type u
| []     []      := One
| []     (a::l)  := Zero
| (a::l) []      := Zero
| (a::l) (b::l') := (a = b) × (list_code l l') 

@[hott, instance]
def list_code_is_prop {A : Set} : Π (l₁ l₂ : list A), is_prop (list_code l₁ l₂)
| []     []      := by change is_prop One; apply_instance
| []     (a::l)  := by change is_prop Zero; apply_instance
| (a::l) []      := by change is_prop Zero; apply_instance
| (a::l) (b::l') := @prod.is_trunc_prod (a = b) (list_code l l') -1 _ 
                                        (list_code_is_prop l l')

@[hott]
def list_refl {A : Set} : Π (l : list A), list_code l l
| []     := One.star
| (a::l) := ⟨idp, list_refl l⟩

@[hott]
def list_decode {A : Set} : Π (l₁ l₂ : list A), list_code l₁ l₂ -> l₁ = l₂
| []     []      := λ lc, idp 
| []     (a::l)  := λ lc, by hinduction lc
| (a::l) []      := λ lc, by hinduction lc
| (a::l) (b::l') := begin 
                      intro lc, hinduction lc, 
                      exact eq.concat (ap (λ a : A, list.cons a l) fst) 
                               (ap (λ l : list A, list.cons b l) (list_decode l l' snd)) 
                    end

@[hott, instance]
def lists_are_set (A : Set) : is_set (list A) :=
begin 
  fapply @encode_decode_set _ list_code list_refl list_code_is_prop, 
  intros a b cd, exact list_decode _ _ cd 
end

end set

end hott