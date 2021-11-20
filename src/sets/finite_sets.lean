import sets.basic

universes u u' v w
hott_theory

namespace hott
open nat is_trunc

namespace set

/- We construct finite sets of arbitrary size using the sum of sets in the induction step. -/
@[hott]
def fin_Set (n : ℕ) : Set.{0} :=
begin hinduction n with n fin_n, exact Zero_Set, exact sum_Set fin_n One_Set end  

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
      { intro f, hinduction f } } }
end

@[hott]
def card_of (S : Set) (fin : is_finite S) : ℕ := fin.1

@[hott]
def fin_Set_bij : ∀ {n m : ℕ}, bijection (fin_Set n) (fin_Set m) -> n = m 
| 0 0 := begin intro bij, refl end
| (succ n) 0 := begin intro bij, hinduction bij.map (sum.inr One.star) end
| 0 (succ m) := begin intro bij, hinduction (inv_of_bijection bij).1 (sum.inr One.star) end
| (succ n) (succ m) := 
  begin 
    intro bij, 
    have bij_n_m : bijection (fin_Set n) (fin_Set m), from sorry,
    exact ap succ (fin_Set_bij bij_n_m) 
  end

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