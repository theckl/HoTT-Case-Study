import sets.subset hott.types.nat.default hott.types.sigma

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc subset hott.sigma

namespace set

/- We construct finite sets of size `n` as the set of natural numbers `m` with `m < n`.
   With this definition we can easily define maps from finite sets to any carrier. -/
@[hott]
def fin_Set (n : ℕ) : Set.{0} := to_Set (Σ m : ℕ, m < n)

@[hott]
def fin_Set_lift {n m : ℕ} (H : n ≤ m) : fin_Set n -> fin_Set m :=
  assume a, ⟨a.1, nat.lt_of_lt_of_le a.2 H⟩

@[hott]
def fin_Set_desc {n m : ℕ} (b : fin_Set m) (H : b.1 < n) : fin_Set n :=
  ⟨b.1, H⟩  

@[hott]
def fin_Set_eq {n : ℕ} {a b : fin_Set n} : a.1 = b.1 -> a = b :=
  assume p, sigma_eq p (pathover_of_tr_eq (is_prop.elim _ _)) 

@[hott]
def fin_Set_lift_desc {n m : ℕ} (H1 : n ≤ m) (b : fin_Set m) (H2 : b.1 < n) :
  fin_Set_lift H1 (fin_Set_desc b H2) = b :=
begin apply fin_Set_eq, refl end  

/- These finte sets can be used to check whether a set is finite and to define the 
   cardinality of finite sets. -/
@[hott]
def is_finite (S : Set) := Σ n : ℕ, bijection S (fin_Set n)

@[hott]
def fin_Set_fin (n : ℕ) : is_finite (fin_Set n) := dpair n (identity (fin_Set n))

@[hott]
def empty_is_fin : is_finite empty_Set :=
begin
  fapply dpair,
  { exact 0 },
  { fapply bijection.mk,
    { intro f, hinduction f },
    { fapply is_set_bijective.mk,
      { intro f, hinduction f },
      { intro f, hinduction hott.nat.not_lt_zero f.1 f.2 } } }
end

@[hott]
def card_of (S : Set) (fin : is_finite S) : ℕ := fin.1

/- Note that inequalities in [types.nat.order] are often theorems, without need, and 
   therefore produce an error because they are assumed to be noncomputable. -/
@[hott]
def fin_Set_bij_succ_map_eq_ineq {n m : ℕ} 
  (bij : bijection (fin_Set (n+1)) (fin_Set (m+1))) {a : fin_Set n} 
  (p : (bij.map (fin_Set_lift (nat.le_succ n) a)).1 = m) :
  (bij.map ⟨n, nat.le_refl (n+1)⟩).1 < m :=
have H1 : (bij ⟨n, nat.le_refl (n+1)⟩).1 ≠ m, from 
  begin 
    intro q, apply λ H : a.1 = n, 
               nat.lt_irrefl n (nat.le_trans (nat.le_of_eq (ap nat.succ H⁻¹)) a.2), 
    have r : (fin_Set_lift (nat.le_succ n) a) = ⟨n, nat.le_refl (n+1)⟩, from 
          begin apply bij.bij.inj, exact fin_Set_eq (p ⬝ q⁻¹) end,
    exact ap sigma.fst r
  end,  
nat.lt_of_le_prod_ne (le_of_succ_le_succ (bij ⟨n, nat.le_refl (n+1)⟩).2) H1

@[hott]
def fin_Set_bij_succ_map_neq_ineq {n m : ℕ} 
  (bij : bijection (fin_Set (n+1)) (fin_Set (m+1))) {a : fin_Set n} 
  (np : (bij.map (fin_Set_lift (nat.le_succ n) a)).1 ≠ m) :
  (bij (fin_Set_lift (nat.le_succ n) a)).1 < m :=
nat.lt_of_le_prod_ne (le_of_succ_le_succ (bij (fin_Set_lift (nat.le_succ n) a)).2) np

@[hott]
def fin_Set_bij_succ_map {n m : ℕ} (bij : bijection (fin_Set (n+1)) (fin_Set (m+1))) :
  fin_Set n -> fin_Set m :=
begin
  let f := bij.map, let g := (inv_of_bijection bij).1,
  intro a, exact (dite ((f (fin_Set_lift (nat.le_succ n) a)).1 = m)
           (λ p, ⟨(f ⟨n, nat.le_refl (n+1)⟩).1, fin_Set_bij_succ_map_eq_ineq bij p⟩) 
  (λ np, ⟨(f (fin_Set_lift (nat.le_succ n) a)).1, fin_Set_bij_succ_map_neq_ineq bij np⟩))
end  

@[hott]
def fin_Set_bij_succ_map_eq {n m : ℕ} (bij : bijection (fin_Set (n+1)) (fin_Set (m+1)))
  {a : fin_Set n} (p : (bij.map (fin_Set_lift (nat.le_succ n) a)).1 = m) :
  fin_Set_bij_succ_map bij a = fin_Set_desc (bij.map ⟨n, nat.le_refl (n+1)⟩) 
                                 (fin_Set_bij_succ_map_eq_ineq bij p) :=
begin change dite _ _ _ = _, rwr dif_pos p end

@[hott]
def fin_Set_bij_succ_map_neq {n m : ℕ} (bij : bijection (fin_Set (n+1)) (fin_Set (m+1)))
  {a : fin_Set n} (np : ¬(bij.map (fin_Set_lift (nat.le_succ n) a)).1 = m) :
  fin_Set_bij_succ_map bij a = fin_Set_desc (bij.map (fin_Set_lift (nat.le_succ n) a)) 
                                 (fin_Set_bij_succ_map_neq_ineq bij np) :=
begin change dite _ _ _ = _, rwr dif_neg np end

@[hott]
def fin_Set_bij_succ_map_inv {n m : ℕ} (bij : bijection (fin_Set (n+1)) (fin_Set (m+1))) :
  is_set_right_inverse_of (fin_Set_bij_succ_map bij) 
                          (fin_Set_bij_succ_map (inv_bijection_of bij)) :=
begin 
  let f := bij.map, let bij_inv := inv_bijection_of bij, let g := bij_inv.map,
  intro b, apply fin_Set_eq, 
  hinduction nat.has_decidable_eq (g (fin_Set_lift (nat.le_succ m) b)).1 n with h p np,
  { have q : (f (fin_Set_lift (le_succ n) (fin_Set_bij_succ_map bij_inv b))).1 = m, by
    begin 
      rwr fin_Set_bij_succ_map_eq bij_inv p, rwr fin_Set_lift_desc, 
      rwr @is_set_inverse_of.r_inv _ _ f g _
    end,
    rwr fin_Set_bij_succ_map_eq bij q, 
    change (bij.map ⟨n, nat.le_refl (n + 1)⟩).1 = (fin_Set_lift (le_succ m) b).1,
    rwr <- @is_set_inverse_of.r_inv _ _ f g _ (fin_Set_lift (le_succ m) b),
    rwr <- @fin_Set_eq _ _ ⟨n, nat.le_refl (n + 1)⟩ p },
  { rwr fin_Set_bij_succ_map_neq bij_inv np, 
    have nq : (f (fin_Set_lift (nat.le_succ n) (fin_Set_desc (bij_inv.map 
                  (fin_Set_lift (le_succ m) b)) (fin_Set_bij_succ_map_neq_ineq 
                                                           bij_inv np)))).1 ≠ m, by
    begin
      rwr fin_Set_lift_desc, rwr @is_set_inverse_of.r_inv _ _ f bij_inv.map _, 
      change b.1 ≠ m, sorry
    end,  
    rwr fin_Set_bij_succ_map_neq bij nq, 
    change (bij.map (fin_Set_lift (le_succ n) (fin_Set_desc (bij_inv.map (fin_Set_lift 
      (le_succ m) b)) (fin_Set_bij_succ_map_neq_ineq bij_inv np)))).1 = b.1, 
    rwr fin_Set_lift_desc, rwr @is_set_inverse_of.r_inv _ _ bij.map bij_inv.map _ }
end    

@[hott]
def fin_Set_succ_bij_bij : ∀ {n m : ℕ}, bijection (fin_Set (n+1)) (fin_Set (m+1)) ->
  bijection (fin_Set n) (fin_Set m) :=
begin 
  intros n m bij, let f := bij.map, let bij_inv := inv_bijection_of bij, 
  let g := bij_inv.map, let f' := fin_Set_bij_succ_map bij, 
  let g' := fin_Set_bij_succ_map bij_inv, fapply has_inverse_to_bijection,
  { exact fin_Set_bij_succ_map bij },
  { exact fin_Set_bij_succ_map bij_inv },
  { fapply is_set_inverse_of.mk, 
    { intro b, apply fin_Set_eq,  
      hinduction nat.has_decidable_eq (g (fin_Set_lift (nat.le_succ m) b)).1 n with h p,
      { have p2 : (f (fin_Set_lift (le_succ n) (fin_Set_bij_succ_map bij_inv b))).1 = m, by
        begin 
          rwr fin_Set_bij_succ_map_eq bij_inv p, rwr fin_Set_lift_desc, 
          rwr @is_set_inverse_of.r_inv _ _ f g,
        end,
        rwr fin_Set_bij_succ_map_eq bij p2, 
        change (bij.map ⟨n, nat.le_refl (n + 1)⟩).1 = (fin_Set_lift (le_succ m) b).1,
        rwr <- @is_set_inverse_of.r_inv _ _ f g (inv_bij_is_inv bij) 
                                                (fin_Set_lift (le_succ m) b),
        rwr <- @fin_Set_eq _ _ ⟨n, nat.le_refl (n + 1)⟩ p },
      { sorry } },
    { intro a, sorry } }
end

@[hott]
def fin_Set_bij : ∀ {n m : ℕ}, bijection (fin_Set n) (fin_Set m) -> n = m 
| 0 0 := begin intro bij, refl end
| (n+1) 0 := begin intro bij, sorry end
| 0 (m+1) := begin intro bij, sorry end
| (n+1) (m+1) := begin intro bij, sorry end

@[hott]
def fin_card_is_uniq {S : Set} : Π (fin₁ fin₂ : is_finite S), fin₁.1 = fin₂.1 :=
  assume fin₁ fin₂,
  have bij : bijection (fin_Set fin₁.1) (fin_Set fin₂.1), from sorry,
  fin_Set_bij  bij


@[hott]
def card_fin_Set {n : ℕ} : card_of (fin_Set n) (fin_Set_fin n) = n := rfl

/- `fin_Set n` can be used to enumerate `n` elements of a (non-empty) set `R`, by 
   exhibiting a map `fin_Set n -> R`. To extract the kth element we construct a list 
   of elements of `R`, of length `n`, and then a function taking the map and the 
   index k, delivering the kth element if `k ≤ n` and a default element otherwise. -/
@[hott, reducible, hsimp]
def fin_Set_to_list {A : Set} {n : ℕ} : (fin_Set n -> A) -> list A :=
begin
  hinduction n, 
  { intro f, exact [] },
  { intros fS, exact (fS (sum.inr One.star)) :: (ih (fS ∘ sum.inl)) }
end 

@[hott]
def fin_Set_list.length {A : Set} {n : ℕ} (f : fin_Set n -> A) :
  list.length (fin_Set_to_list f) = n :=
begin
  hinduction n, 
  { refl },
  { exact ap succ (ih (f ∘ sum.inl)) }
end    

@[hott]
def fin_Set_kth {n : ℕ} {R : Set} [r : inhabited R] (f : fin_Set n -> R) (k : ℕ) : R :=    
begin
  fapply @nat.lt_ge_by_cases k n _, 
  { rwr <- fin_Set_list.length f, intro lt, 
    exact list_nth_le (fin_Set_to_list f) k lt },
  { intro lt, exact r.default } 
end  

notation x `^[` k `]` := fin_Set_kth x k

/- We can also produce a `fin_Set` from a list, and the two operations are inverse to 
   each other. -/
@[hott, reducible, hsimp]
def list_to_fin_Set {A : Set} : Π l : list A, (fin_Set (list.length l) -> A) :=
begin
  intro l, hinduction l,  
  { intro fin_el, hinduction fin_el },
  { intro finS_el, hinduction finS_el, 
    { exact ih val },
    { exact hd } }
end  

@[hott]
def rinv_fin_Set_list (A : Set) : 
  ∀ l : list A, fin_Set_to_list (list_to_fin_Set l) = l :=
begin
  intro l, hinduction l,
  { refl },
  { have H : (list_to_fin_Set (hd :: tl)) =  
               @sum.rec _ One (λ s, A) (list_to_fin_Set tl) (λ s, hd), from rfl,
    have H' : @fin_Set_to_list A (list.length (hd::tl)) 
                (@sum.rec _ One (λ s, A) (list_to_fin_Set tl) (λ s, hd)) =
                  hd :: (fin_Set_to_list (list_to_fin_Set tl)), from rfl,
    rwr H, rwr H', rwr ih } 
end

@[hott]
def linv_fin_Set_list (A : Set) {n : ℕ}: 
  ∀ f : fin_Set n -> A, list_to_fin_Set (fin_Set_to_list f) 
                              =[fin_Set_list.length f; λ m, fin_Set m -> A] f :=
begin
  intro f, apply pathover_of_tr_eq, apply eq_of_homotopy, intro s, hinduction n, 
  { hinduction s },
  { hinduction s with s s, 
    { rwr tr_dep_fn_eval_tr (fin_Set_list.length f) _, 
      have H : ((fin_Set_list.length f)⁻¹ ▸[λ m, ↥(fin_Set m)] sum.inl s) = 
                           sum.inl ((fin_Set_list.length (f ∘ sum.inl))⁻¹ ▸ s), from 
      begin 
        change ((ap succ (fin_Set_list.length (f ∘ sum.inl)))⁻¹ ▸[λ m, ↥(fin_Set m)] 
                                                                           sum.inl s) = _,
        rwr <- ap_inv _ _, exact ap_tr_fn succ (λ (n : ℕ) (s : fin_Set n), sum.inl s) _ s
      end,
      rwr H, 
      calc (list_to_fin_Set (fin_Set_to_list (f ∘ sum.inl))) _ = 
                 (fin_Set_list.length (f ∘ sum.inl) ▸[λ m, fin_Set m -> A.carrier] 
                                  list_to_fin_Set (fin_Set_to_list (f ∘ sum.inl))) s : 
                 (@tr_dep_fn_eval_tr ℕ ↥A (λ m, fin_Set m) _ _ 
                      (list_to_fin_Set (fin_Set_to_list (f ∘ sum.inl)))
                                           (fin_Set_list.length (f ∘ sum.inl)) s)⁻¹
           ... = (f ∘ sum.inl) s : ih s (f ∘ sum.inl) },
    { rwr tr_dep_fn_eval_tr (fin_Set_list.length f) _, 
      have H' : ((fin_Set_list.length f)⁻¹ ▸[λ m, ↥(fin_Set m)] sum.inr s) = sum.inr s, from
      begin 
        hinduction sum.mem_cases ((fin_Set_list.length f)⁻¹ ▸[λ m, ↥(fin_Set m)] sum.inr s), 
        { have H'' : (fin_Set_list.length f) ▸[λ m, ↥(fin_Set m)] sum.inl val.1 = 
            sum.inl ((fin_Set_list.length (f ∘ sum.inl)) ▸[λ m, ↥(fin_Set m)] val.1), from 
          begin 
            change (ap succ (fin_Set_list.length (f ∘ sum.inl))) ▸[λ m, ↥(fin_Set m)] 
                                                                        sum.inl val.1 = _, 
            exact ap_tr_fn succ (λ (n : ℕ) (s : fin_Set n), sum.inl s) _ val.1
          end,
          let p := val.2, let p' := eq_tr_of_inv_tr_eq p, rwr H'' at p', 
          hinduction sum_encode p', hinduction down },
        { let p := val.2, rwr p, exact ap sum.inr (@is_prop.elim _ One_is_prop _ _) } 
      end,
      calc list_to_fin_Set (fin_Set_to_list f) ((fin_Set_list.length f)⁻¹ 
                                                  ▸[λ m, ↥(fin_Set m)] sum.inr s) = 
                 list_to_fin_Set (fin_Set_to_list f) (sum.inr s) : by rwr H'
           ... = f (sum.inr One.star) : rfl 
           ... = f (sum.inr s) : by rwr is_prop.elim One.star s } }
end

@[hott, hsimp]
def fin_Set_eq_map {n m : ℕ} (p : n = m) : fin_Set n -> fin_Set m := 
  λ s : fin_Set n, p ▸ s

@[hott]
def fin_Set_eq_map_inl {n m : ℕ} (p : n = m) (s : fin_Set n) :
  fin_Set_eq_map (ap succ p) (sum.inl s) = sum.inl (fin_Set_eq_map p s) :=
begin hinduction p, refl end  

@[hott]
def fin_Set_eq_map_inr {n m : ℕ} (p : n = m) (s : One_Set) :
  fin_Set_eq_map (ap succ p) (sum.inr s) = sum.inr s :=
begin hinduction p, refl end  

@[hott]
def list_to_fin_Set_map {A B : Set} (f : A -> B) (l : list A) :
  f ∘ (list_to_fin_Set l) = (list_to_fin_Set (list.map f l)) ∘ 
                            (fin_Set_eq_map (list_map_size_eq f l)⁻¹) :=
begin 
  apply eq_of_homotopy, intro s, hinduction l, 
  { hinduction s },
  { have p : (ap succ (list_map_size_eq f tl)⁻¹) = 
                        ((list_map_size_eq f (hd :: tl))⁻¹), from is_prop.elim _ _,
    hinduction s with s s,
    { rwr ih s, rwr <- p, 
      change _ = (list_to_fin_Set (list.map f (hd :: tl))) 
                   (fin_Set_eq_map (ap succ (list_map_size_eq f tl)⁻¹) (sum.inl s)),
      rwr fin_Set_eq_map_inl (list_map_size_eq f tl)⁻¹ s },
    { change f hd = (list_to_fin_Set (list.map f (hd :: tl))) 
                    ((fin_Set_eq_map (list_map_size_eq f (hd :: tl))⁻¹) (sum.inr s)), 
      rwr <-p, rwr fin_Set_eq_map_inr (list_map_size_eq f tl)⁻¹ s } } 
end  

end set

end hott