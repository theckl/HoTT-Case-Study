import hott.init hott.hit.trunc hott.types.trunc hott.types.nat.order types2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat unit

/- Facts about natural numbers not found in the [HoTT3]-library (or only as theorems). -/
open nat

/- We introduce several characterisation of a "natural system" natural types, using the 
   constructors of ℕ, and show that they imply each other.  -/
@[hott]  --[GEVE]
structure is_cons_nat_type (N : Type _) :=
  (zero : N)
  (succ : N -> N)
  (iter : Π (n : N), Σ (i : nat), hott.iterate succ i zero = n)
  (unique : Π (i i' : nat), hott.iterate succ i zero = hott.iterate succ i' zero -> i = i')

@[hott]
def nat_iter_zero {N : Type} (is_nat : is_cons_nat_type N) :
  (is_nat.iter is_nat.zero).1 = 0 :=
is_nat.unique _ _ (is_nat.iter is_nat.zero).2


@[hott]
def nat_iter_succ {N : Type} (is_nat : is_cons_nat_type N) :
  Π (n : N), (is_nat.iter (is_nat.succ n)).1 = nat.succ (is_nat.iter n).1 :=
begin
  intro n, 
  fapply is_nat.unique, apply eq.concat (is_nat.iter (is_nat.succ n)).2, 
  apply ap is_nat.succ, 
  have p : hott.iterate is_nat.succ (is_nat.iter n).1 is_nat.zero = n, from 
    (is_nat.iter n).2,
  rwr p
end

@[hott]   --[GEVE]
def ℕ_is_cons_nat_type : is_cons_nat_type ℕ :=
begin 
  fapply is_cons_nat_type.mk,
  { exact 0 },
  { exact nat.succ },
  { intro n, apply dpair n, exact nth_iter_eq_n n },
  { intro i, hinduction i, 
    { intro i', hinduction i', 
      { intro p, exact idp }, 
      { intro p, change 0 = succ _ at p, exact empty.elim (nat.succ_ne_zero _ p⁻¹) } },
    { intro i', hinduction i', 
      { intro p, change succ _ = 0 at p, exact empty.elim (nat.succ_ne_zero _ p) },
      { intro p, change succ _ = succ _ at p, exact ap succ (ih _ (succ.inj p)) } } }   
end

@[hott]
structure cons_nat_type :=
  (carrier : Type _)
  (is_nat : is_cons_nat_type carrier)

@[hott]  --[GEVE]
structure is_ind_nat_type (N : Type _) :=
  (zero : N)
  (succ : N -> N)
  (map : Π {A : Type _} (a₀ : A) (s : A -> A), Σ (f : N -> A), (f zero = a₀) × 
                                                       (Π (n : N), f (succ n) = s (f n)))
  (unique : Π {A : Type _} (a₀ : A) (s : A -> A) (f f' : N -> A), (f zero = f' zero) -> 
                            (Π (n : N), f (succ n) = s (f n)) ->
                                            (Π (n : N), f' (succ n) = s (f' n)) -> f = f')

@[hott]  --[GEVE]
def nat_cons_to_ind_type {N : Type _} : is_cons_nat_type N -> is_ind_nat_type N :=
begin
  intro is_nat, fapply is_ind_nat_type.mk,
  { exact is_nat.zero },
  { exact is_nat.succ },
  { intros A a₀ s, fapply dpair,
    { intro n, exact hott.iterate s (is_nat.iter n).1 a₀ },
    { fapply prod.mk,
      { rwr nat_iter_zero is_nat },
      { intro n, rwr nat_iter_succ is_nat n } } },
  { intros A a₀ s f f' f_f'_0_eq f_s_eq f'_s_eq, apply eq_of_homotopy, intro n,
    hinduction (is_nat.iter n) with iter_eq i, rwr <- snd, 
    clear iter_eq snd n, hinduction i, 
    { exact f_f'_0_eq },
    { change f (is_nat.succ _) = f' (is_nat.succ _), 
      rwr f_s_eq ((is_nat.succ^[n] is_nat.zero)),
      rwr f'_s_eq ((is_nat.succ^[n] is_nat.zero)), exact ap s ih } }
end

@[hott]  --[GEVE]
def nat_ind_to_cons_type {N : Type _} : is_ind_nat_type N -> is_cons_nat_type N :=
begin  
  intro is_nat, fapply is_cons_nat_type.mk, 
  { exact is_nat.zero },
  { exact is_nat.succ },
  { intro n, fapply dpair,
    { exact (is_nat.map 0 nat.succ).1 n },
    { apply λ p, ap10 p n, fapply is_nat.unique is_nat.zero is_nat.succ,
      { rwr (is_nat.map 0 nat.succ).2.1 },
      { intro n, rwr (is_nat.map 0 nat.succ).2.2 },
      { intro n, exact idp } } },
  { intros i i' iter_eq, 
    have p : Π (n : ℕ), (is_nat.map 0 nat.succ).1 (is_nat.succ^[n] is_nat.zero) = n, from
    begin 
      intro n, hinduction n, exact (is_nat.map 0 nat.succ).2.1, 
      change (is_nat.map 0 succ).fst (is_nat.succ _) = _, 
      rwr (is_nat.map 0 nat.succ).2.2, exact ap succ ih 
    end, 
    rwr <- p i, rwr <- p i', exact ap (is_nat.map 0 nat.succ).1 iter_eq }
end

/- Characterising natural types by extracting the number of iterations of the succesor 
   function needed to produce a given element from zero is most effective to verify that
   `ℕ` and `binℕ` are natural types, and that natural types are ``canonically" equal. 
   
   We also prove that this characterisation is equivalent to the characterisation by 
   constructors. -/
@[hott]  --[GEVE]
structure is_ext_nat_type (N : Type _) :=
  (iter : N → ℕ)
  (exist : Π (i : ℕ), Σ (n : N), iter n = i)
  (unique : Π (n n' : N), iter n = iter n' -> n = n')

@[hott]  --[GEVE]
def ext_nat_type_linv {N : Type _} (is_nat : is_ext_nat_type N) : 
  Π (n : N), (is_nat.exist (is_nat.iter n)).fst = n :=
λ n, is_nat.unique _ _ (is_nat.exist (is_nat.iter n)).2

@[hott]   --[GEVE]
def ext_nat_type_rinv {N : Type _} (is_nat : is_ext_nat_type N) : 
  Π (n : ℕ), is_nat.iter (is_nat.exist n).fst = n :=
λ n, (is_nat.exist n).2 

@[hott, reducible]
def ext_nat_type_equiv_nat {N : Type _} : is_ext_nat_type N -> N ≃ ℕ :=
begin
  intro is_nat, fapply equiv.mk,
  { exact is_nat.iter },
  { fapply adjointify,
    { intro i, exact (is_nat.exist i).1 },
    { intro i, exact ext_nat_type_rinv is_nat i },
    { intro n, exact ext_nat_type_linv is_nat n } }
end

@[hott]
def ℕ_is_ext_nat_type : is_ext_nat_type ℕ :=
begin 
  fapply is_ext_nat_type.mk,
  { exact id },
  { intro i, exact dpair i idp },
  { intros n n' iter_eq, exact iter_eq }   
end

@[hott]  --[GEVE]
def binℕ_is_ext_nat_type : is_ext_nat_type binℕ :=
begin 
  fapply is_ext_nat_type.mk,
  { exact binℕ_to_nat },
  { intro i, fapply dpair, exact nat_to_binℕ i, exact nat_binℕ.left_inv i },
  { intros n n', intro p, rwr <- nat_binℕ.right_inv n, rwr <- nat_binℕ.right_inv n',
    exact ap nat_to_binℕ p }   
end

@[hott, instance]  --[GEVE]
def ext_nat_type_is_set {N : Type _} : is_ext_nat_type N -> is_set N :=
begin  
  intro is_nat, apply is_trunc_equiv_closed_rev 0 (ext_nat_type_equiv_nat is_nat),
  apply_instance
end

@[hott]
structure ext_nat_type :=
  (carrier : Type _)
  (is_nat : is_ext_nat_type carrier)

@[hott, reducible]
def ext_nat_type_nat : ext_nat_type :=
  ext_nat_type.mk ℕ ℕ_is_ext_nat_type 

@[hott]
def nat_type_equiv_Sigma : ext_nat_type ≃ Σ (N : Type _), is_ext_nat_type N :=
begin
  fapply equiv.mk,
  { intro nat_type, exact dpair nat_type.carrier nat_type.is_nat },
  { fapply adjointify,
    { intro sigma_nat_type, exact ext_nat_type.mk sigma_nat_type.1 sigma_nat_type.2 },
    { intro nat_type, hinduction nat_type, exact idp },
    { intro sigma_nat_type, hinduction sigma_nat_type, exact idp } }
end

@[hott]
def nat_type_dep_id_sys : dep_ppred ℕ ℕ_is_ext_nat_type :=
begin
  fapply dep_ppred.mk,
  { exact id_ppred ℕ },
  { intros N is_nat_N p, 
    exact prod (is_nat_N.iter =[p⁻¹; λ N : Type, N -> ℕ] id) 
               ((λ i : ℕ, (is_nat_N.exist i).1) =[p⁻¹; λ N : Type, ℕ -> N] id) },
  { exact ⟨idpo, idpo⟩ }
end

@[hott, instance] 
def ℕ_dep_id_sys_is_prop (is_nat : is_ext_nat_type ℕ) : 
  is_prop (nat_type_dep_id_sys.dep_fam ℕ is_nat nat_type_dep_id_sys.ppred_fst.base) :=
begin change is_prop (prod (_ =[idp] _) (_ =[idp] _)), apply_instance end

@[hott]
def nat_type_eq_contr : is_contr (Σ (is_nat : is_ext_nat_type ℕ), 
  nat_type_dep_id_sys.dep_fam ℕ is_nat nat_type_dep_id_sys.ppred_fst.base) :=
begin
  fapply is_contr.mk,
  { exact dpair ℕ_is_ext_nat_type (pair idpo idpo) },
  { intro is_nat, hinduction is_nat with is_nat is_nat_eq,
    change prod (_ =[idp] _) (_ =[idp] _) at is_nat_eq, 
    fapply sigma.sigma_eq,
    { hinduction is_nat, 
      have q₁ : id = iter, from (eq_of_pathover_idp is_nat_eq.1)⁻¹,
      hinduction q₁, fapply apd0111' is_ext_nat_type.mk,
      { exact idp },
      { apply pathover_idp_of_eq, apply eq_of_homotopy, intro i, fapply sigma.sigma_eq,
        exact ap10 (eq_of_pathover_idp is_nat_eq.2)⁻¹ i,
        apply pathover_of_tr_eq, exact is_prop.elim _ _ },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott]
def nat_type_eq_ℕ (nat_type_Sigma : Σ (N : Type), is_ext_nat_type N) :
  Σ (p : ℕ = nat_type_Sigma.1),
    nat_type_dep_id_sys.dep_fam nat_type_Sigma.1 nat_type_Sigma.2 p := 
begin
  fapply dpair,
  { exact ua (ext_nat_type_equiv_nat nat_type_Sigma.2)⁻¹ᵉ },
  { fapply prod.mk,
    { apply fn_pathover_equiv_of_eq, 
      rwr equiv.ua_symm, rwr hott.eq.inv_inv, rwr equiv_of_eq_ua },
    { apply fn_pathover_equiv_of_eq', 
      rwr equiv.ua_symm, rwr hott.eq.inv_inv, rwr equiv_of_eq_ua,
      apply eq_of_homotopy, intro n, apply eq.inverse,
      exact is_equiv.right_inv (ext_nat_type_equiv_nat nat_type_Sigma.snd).to_fun n } }
end

@[hott] --[GEVE]
def ext_nat_types_are_canonically_equal : is_contr ext_nat_type :=
begin
  apply is_trunc_equiv_closed_rev -2 nat_type_equiv_Sigma,
  fapply is_contr.mk,
  { exact dpair ℕ ℕ_is_ext_nat_type },
  { intro nat_type, 
    exact (struct_id_char_of_contr _ nat_type_dep_id_sys (is_contr_tot_peq _) 
            nat_type_eq_contr nat_type)⁻¹ᶠ (nat_type_eq_ℕ nat_type) }     
end

@[hott]  --[GEVE]
def cons_to_ext_nat_type {N : Type _} : is_cons_nat_type N -> is_ext_nat_type N :=
begin
  intro is_nat, fapply is_ext_nat_type.mk,
  { intro n, exact (is_nat.iter n).1 },
  { intro i, induction i,
    { exact dpair is_nat.zero (nat_iter_zero is_nat) },
    { rwr <- i_ih.2, exact dpair (is_nat.succ i_ih.1) (nat_iter_succ is_nat i_ih.1) } },
  { intros n n' iter_eq, rwr <- (is_nat.iter n).2, rwr <- (is_nat.iter n').2,
    exact ap (λ i, hott.iterate is_nat.succ i is_nat.zero) iter_eq }
end

@[hott]  --[GEVE]
def ext_to_cons_nat_type {N : Type _} : is_ext_nat_type N -> is_cons_nat_type N :=
begin
  intro is_nat, fapply is_cons_nat_type.mk,
    { exact (is_nat.exist 0).1 },
    { exact λ c, (is_nat.exist (nat.succ (is_nat.iter c))).1 },
    { intro c, fapply dpair, 
      { exact is_nat.iter c },
      { rwr @fn_eq_iterate _ _ (λ n, (is_nat.exist n).1) nat.succ is_nat.iter
                           (ext_nat_type_linv is_nat) (ext_nat_type_rinv is_nat) _
                               (is_nat.exist 0).fst,
        { rwr ext_nat_type_rinv is_nat 0, rwr nth_iter_eq_n, 
          change (is_nat.exist _).1 = _, rwr ext_nat_type_linv is_nat c } } },
    { intros i i', 
      rwr @fn_eq_iterate _ _ (λ n, (is_nat.exist n).1) nat.succ is_nat.iter 
                         (ext_nat_type_linv is_nat) (ext_nat_type_rinv is_nat) _ 
                               (is_nat.exist 0).fst,
      rwr @fn_eq_iterate _ _ (λ n, (is_nat.exist n).1) nat.succ is_nat.iter 
                         (ext_nat_type_linv is_nat) (ext_nat_type_rinv is_nat) _ 
                               (is_nat.exist 0).fst,
      rwr ext_nat_type_rinv is_nat 0, rwr nth_iter_eq_n, rwr nth_iter_eq_n,
      intro p, rwr <- ext_nat_type_rinv is_nat i, rwr <- ext_nat_type_rinv is_nat i',
      exact ap is_nat.iter p } 
end

@[hott]  --[GEVE]
structure is_term_nat_type (N : Type _) :=
  (iter : N -> ℕ)
  (map : Π {A : Type _} (j : A -> ℕ), Σ (f : A -> N), j = iter ∘ f)
  (unique : Π {A : Type _} (f f' : A -> N), iter ∘ f = iter ∘ f' -> f = f')

@[hott]   --[GEVE]
def ext_to_term_nat_type {N : Type _} : is_ext_nat_type N -> is_term_nat_type N :=
begin
  intro is_nat, fapply is_term_nat_type.mk, 
  { exact is_nat.iter },
  { intros A j, fapply dpair,
    { intro a, exact (is_nat.exist (j a)).1 },
    { apply eq_of_homotopy, intro a, exact (is_nat.exist (j a)).2⁻¹ } },
  { intros A f f' iter_eq, apply eq_of_homotopy, intro a, 
    exact is_nat.unique _ _ (ap10 iter_eq a) }
end

@[hott]  --[GEVE]
def term_to_ext_nat_type {N : Type _} : is_term_nat_type N -> is_ext_nat_type N :=
begin
  intro is_nat, fapply is_ext_nat_type.mk, 
  { exact is_nat.iter },
  { intro i, fapply dpair,
    { exact (is_nat.map (λ i : ℕ, i)).1 i },
    { change (is_nat.iter ∘ (is_nat.map (λ (i : ℕ), i)).fst) i = _,
      rwr <- ap10 (is_nat.map (λ i : ℕ, i)).2 i } },
  { intros n n' iter_eq,
    let f := @punit.rec (λ u, N) n, let f' := @punit.rec (λ u, N) n',
    change f unit.star = f' unit.star,
    change is_nat.iter (f unit.star) = is_nat.iter (f' unit.star) at iter_eq,
    have iter_comp_eq : is_nat.iter ∘ f = is_nat.iter ∘ f', from
      begin apply eq_of_homotopy, intro u, hinduction u, exact iter_eq end,
    exact ap10 (is_nat.unique f f' iter_comp_eq) unit.star }
end

end hott