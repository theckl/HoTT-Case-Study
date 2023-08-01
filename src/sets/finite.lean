import sets.subset hott.types.nat.default hott.types.sigma

universes u u' v w
hott_theory

namespace hott
open hott.nat is_trunc trunc subset hott.sigma

namespace set

/- We construct finite sets of size `n` as the set of natural numbers `m` with `m < n`.
   With this definition we can easily define maps from finite sets to any carrier type. -/
@[hott]
def fin_Set (n : ℕ) : Set.{0} := to_Set (Σ m : ℕ, m < n)

@[hott]
def fin_Set_lift {n m : ℕ} (H : n ≤ m) : fin_Set n -> fin_Set m :=
  assume a, ⟨a.1, nat.lt_of_lt_of_le a.2 H⟩

@[hott, hsimp]
def fin_Set_desc {n m : ℕ} (b : fin_Set m) (H : b.1 < n) : fin_Set n :=
  ⟨b.1, H⟩  

@[hott]
def fin_Set_eq {n : ℕ} {a b : fin_Set n} : a.1 = b.1 -> a = b :=
  assume p, sigma_eq p (pathover_of_tr_eq (is_prop.elim _ _)) 

@[hott]
def fin_Set_lift_desc {n m : ℕ} (H1 : n ≤ m) (b : fin_Set m) (H2 : b.1 < n) :
  fin_Set_lift H1 (fin_Set_desc b H2) = b :=
begin apply fin_Set_eq, refl end  

/- These finite sets can be used to check whether a set is finite and to define the 
   cardinality of finite sets. 
   
   We can show that finiteness is a predicate on sets, so we can use it as a class. -/
@[hott]
class is_finite (S : Set) := 
  (fin_bij : Σ n : ℕ, bijection S (fin_Set n))

@[hott, instance]
def fin_Set_fin (n : ℕ) : is_finite (fin_Set n) := 
  is_finite.mk (dpair n (identity (fin_Set n)))

@[hott, instance]
def empty_is_fin : is_finite empty_Set :=
begin
  apply is_finite.mk, fapply dpair,
  { exact 0 },
  { fapply bijection.mk,
    { intro f, hinduction f },
    { fapply is_set_bijective.mk,
      { intro f, hinduction f },
      { intro f, hinduction hott.nat.not_lt_zero f.1 f.2 } } }
end

@[hott]
def empty_fin_Set_map (C : Type _) : fin_Set 0 -> C :=
begin intro f, hinduction (not_lt_zero f.1 f.2) end

@[hott]
def empty_fin_Set_map_comp {C D : Type _} : Π (f : C -> D), 
  f ∘ (empty_fin_Set_map C) = empty_fin_Set_map D :=
begin intro f, apply eq_of_homotopy, intro a, hinduction (not_lt_zero a.1 a.2) end 

@[hott, hsimp]
def fin_map_ind {C : Type _} {n : ℕ} : Π (f : fin_Set n -> C) (c : C), 
  (fin_Set (n+1) -> C) :=
begin
  intros f c m, fapply dite (m.1 = n), 
  { intro p, exact c },
  { intro np, exact f (fin_Set_desc m (nat.lt_of_le_prod_ne (nat.le_of_lt_succ m.2) np)) }
end 

@[hott]
def fin_card_of (S : Set) [fin : is_finite S] : ℕ := fin.fin_bij.1

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
      change b.1 ≠ m, 
      exact λH1, nat.lt_irrefl m (nat.le_trans (nat.le_of_eq (ap nat.succ H1⁻¹)) b.2)
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
    { exact fin_Set_bij_succ_map_inv bij },
    { change is_set_right_inverse_of (fin_Set_bij_succ_map bij_inv) 
                                     (fin_Set_bij_succ_map bij),
      rwr bij_is_inv_of_bij_inv bij, exact fin_Set_bij_succ_map_inv bij_inv } }
end

@[hott]
def fin_Set_bij : ∀ {n m : ℕ}, ∥bijection (fin_Set n) (fin_Set m)∥ -> n = m :=
begin
  intro n, hinduction n, 
  { intro m, hinduction m with m,
    { intro bij, refl },
    { intro bij, hinduction bij with bij,
      hinduction not_succ_le_zero ((inv_bijection_of bij).map ⟨0, zero_lt_succ m⟩).1 
                                  ((inv_bijection_of bij).map ⟨0, zero_lt_succ m⟩).2 } },
  { intro m, hinduction m with m, 
    { intro bij, hinduction bij with bij, 
      hinduction not_succ_le_zero (bij.map ⟨n, nat.le_refl _⟩).1 
                                  (bij.map ⟨n, nat.le_refl _⟩).2 },
    { intro bij, hinduction bij with bij, 
      exact ap nat.succ (@ih m (tr (fin_Set_succ_bij_bij bij))) } }
end    

@[hott]
def card_fin_Set {n : ℕ} : fin_card_of (fin_Set n) = n := rfl

/- `fin_Set n` can be used to enumerate `n` elements of a (non-empty) set `A`, by 
   exhibiting a map `fin_Set n -> A`. To extract the kth element we construct a function 
   `ℕ -> A` taking the map and the index k, delivering the kth element if `k ≤ n` and a 
   default element otherwise. -/
@[hott]
def fin_Set_kth {n : ℕ} {A : Set} [r : inhabited A] (f : fin_Set n -> A) (k : ℕ) : A :=    
begin
  fapply @nat.lt_ge_by_cases k n _, 
  { intro p, exact f ⟨k, p⟩ },
  { intro lt, exact r.default } 
end  

notation x `^[` k `]` := fin_Set_kth x k 

/- We can use lists of objects of `C` to construct maps from finite sets into `C`. -/
@[hott, hsimp] 
def fin_map_of_list {C : Type _} (l : list C) : fin_Set (list.length l) -> C :=
begin 
  hinduction l,
  { exact empty_fin_Set_map C },
  { exact fin_map_ind ih hd } 
end

/- Finite sets have decidable equality. -/
@[hott]
def fin_Set_is_decidable {n : ℕ} : Π (m₁ m₂ : fin_Set n), (m₁ = m₂) ⊎ ¬(m₁ = m₂) :=
begin
  intros m₁ m₂, hinduction m₁ with m₁ bd₁, hinduction m₂ with m₂ bd₂, 
  hinduction nat_eq_is_decidable m₁ m₂, 
    apply sum.inl, fapply sigma_eq, exact val, apply pathover_of_tr_eq, 
                                               exact is_prop.elim _ _,
    apply sum.inr, intro p, exact val (ap sigma.fst p)
end


/- For first-order languages we need finiteness of decidable subsets. -/
@[hott]
class is_finite_dec_sset {A : Set} (B : dec_Subset A) :=
  (fin : is_finite (pred_Set (dec_sset_to_sset B)))

@[hott]
structure fin_dec_Subset {A : Set} :=
  (sset : dec_Subset A)
  (is_fin : is_finite_dec_sset sset)

attribute [instance] fin_dec_Subset.is_fin 

/- Decidable singleton subsets are finite. -/
@[hott, instance]
def singleton_dec_sset_fin {A : Set} (a : A) [H : decidable_eq A] : 
  is_finite_dec_sset (singleton_dec_sset a) :=
begin 
  apply is_finite_dec_sset.mk, apply is_finite.mk, fapply sigma.mk, exact 1,
  fapply has_inverse_to_bijection, 
  { exact λ a, ⟨0, nat.le_refl 1⟩ },
  { intro m, fapply sigma.mk, exact a,
    have p : singleton_dec_sset a a = Two.one, from sorry, 
    change ↥(@Two.rec (λ t, Prop) _ _ _), rwr p, exact true.intro, },
  { fapply is_set_inverse_of.mk, 
    { sorry },
    { sorry } }  
end

/- A finite subset of a set with decidable equality is decidable. -/
@[hott]
def fin_map_to_dec_sset {A : Set} [H : decidable_eq A] : 
  Π {n : ℕ}, ((fin_Set n) -> A) -> dec_Subset A 
| 0     := λ map a, Two.zero 
| (n + 1) := λ map a, @decidable.rec (map ⟨n, nat.le_refl (n+1)⟩ = a) (λ s, Two) 
                        (λ v, Two.one) 
                        (λ nv, fin_map_to_dec_sset (λ m, map ⟨m.1, nat.le.step m.2⟩) a) 
                        (H (map ⟨n, nat.le_refl (n+1)⟩) a) 
      
@[hott]
def fin_map_to_dec_sset_ind {A : Set} [H : decidable_eq A] {n : ℕ} 
  (f : (fin_Set (n+1)) -> A) {a : A} (ne : ¬ f ⟨n, nat.le_refl (n+1)⟩ = a) : 
  fin_map_to_dec_sset f a = fin_map_to_dec_sset (λ m, f ⟨m.1, nat.le.step m.2⟩) a :=
begin 
  change @decidable.rec _ (λs, Two) _ _ (H (f ⟨n, nat.le_refl (n+1)⟩) a) = _, 
  hinduction (H (f ⟨n, nat.le_refl (n+1)⟩) a), 
  { hinduction ne a_1 },
  { refl }
end 

@[hott]
def fin_map_to_dec_sset_elem {A : Set} [H : decidable_eq A] : 
  Π (n : ℕ) (a : A) (f : (fin_Set n) -> A), fin_map_to_dec_sset f a = Two.one ->
                                            Σ m : fin_Set n, f m = a :=
begin 
  intro n, hinduction n, 
  { intros a f eq, change Two.zero = _ at eq, hinduction encode_Two _ _ eq },
  { intros a f eq, hinduction H (f ⟨n, nat.le_refl (n+1)⟩) a,
      exact dpair ⟨n, nat.le_refl (n+1)⟩ a_1, 
      rwr fin_map_to_dec_sset_ind f a_1 at eq, 
      let peq := ih a (λ (m : (fin_Set n)), f ⟨m.fst, nat.le.step m.snd⟩) eq, 
      fapply sigma.mk,  
        exact sigma.mk peq.1.1 (nat.le.step peq.1.2),
        exact peq.2 }
end 

@[hott]
def fin_map_to_dec_sset_elem' {A : Set} [H : decidable_eq A] : 
  Π (n : ℕ) (a : A) (f : (fin_Set n) -> A), (Σ m : fin_Set n, f m = a) ->
                                            fin_map_to_dec_sset f a = Two.one :=
begin
  intro n, hinduction n, 
  { intros a f m_eq, hinduction nat.not_lt_zero m_eq.1.1 m_eq.1.2 },
  { intros a f m_eq, hinduction H (f ⟨n, nat.le_refl (n+1)⟩) a, 
      change @decidable.rec _ (λs, Two) _ _ (H (f ⟨n, nat.le_refl (n+1)⟩) a) = _, rwr _h, 
      rwr fin_map_to_dec_sset_ind f a_1, fapply ih, 
      hinduction nat.eq_sum_lt_of_le m_eq.1.2,
        have p : m_eq.1 = ⟨n, nat.le_refl (n + 1)⟩, from 
          begin 
            fapply sigma.sigma_eq, exact nat.succ.inj val, 
            apply pathover_of_tr_eq, exact is_prop.elim _ _
          end,
        rwr <- p at a_1, hinduction a_1 m_eq.2,
        fapply sigma.mk,
          exact sigma.mk m_eq.1.1 (nat.le_of_succ_le_succ val),
          rwr <- m_eq.2, apply ap f, hinduction m_eq.1, 
          fapply sigma.sigma_eq, refl, apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end 

@[hott]
def finite_sset_to_dec_sset {A : Set} [decidable_eq A] (B : Subset A) 
  [H : is_finite (pred_Set B)] : dec_Subset A :=
fin_map_to_dec_sset (pred_Set_map B ∘ inv_bijection_of H.fin_bij.2)

@[hott]
def finite_dec_sset_is_sset {A : Set} [decidable_eq A] (B : Subset A) 
  [H : is_finite (pred_Set B)] : dec_sset_to_sset (finite_sset_to_dec_sset B) = B :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, hinduction finite_sset_to_dec_sset B a with p, 
    { change ↥(@Two.rec (λ t, Prop) _ _ (finite_sset_to_dec_sset B a)) at inc, 
      rwr p at inc, hinduction inc },
    { let m_eq := fin_map_to_dec_sset_elem _ _ _ p, rwr <- m_eq.2, 
      exact ((inv_bijection_of (is_finite.fin_bij (pred_Set B)).2).1 m_eq.1).2 } },
  { intros a inc, change ↥(@Two.rec (λ t, Prop) _ _ (finite_sset_to_dec_sset B a)),
    hinduction finite_sset_to_dec_sset B a with p, 
    { have p' : finite_sset_to_dec_sset B a = Two.one, from 
      begin 
        fapply fin_map_to_dec_sset_elem', fapply sigma.mk,
          exact H.fin_bij.2 ⟨a, inc⟩,
          change pred_Set_map B _ = a, rwr inv_bij_l_inv
      end,
      rwr p' at p, hinduction encode_Two _ _ p },
    { exact true.intro } }
end

end set

end hott