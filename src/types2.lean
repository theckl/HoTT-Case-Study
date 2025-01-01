import hott.init hott.hit.trunc hott.types.trunc hott.types.nat.order init2 nat2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat 

/- Properties of the product of two types -/
@[hott]
def all_prod_all {I J : Type _} (F : I -> J -> Type _) : 
  (∀ p : I × J, F p.1 p.2) -> ∀ (i : I) (j : J), F i j :=
assume all_prod i j, all_prod ⟨i,j⟩  

/- An extended elimination principle for truncations -/
@[hott]
def trunc.elim2 {n : ℕ₋₂} {A : Type _} {B : Type _} {P : Type _} [Pt : is_trunc n P] : 
  (A → B -> P) → trunc n A → trunc n B -> P :=
begin intros f tA tB, exact untrunc_of_is_trunc (trunc_functor2 f tA tB) end  

/- Some useful facts on identities of Σ-types and pairs. -/
@[hott]
def sigma_Prop_eq {A : Type _} {B : Π a : A, Prop} (s₁ s₂ : Σ (a : A), B a) : 
  s₁.1 = s₂.1 -> s₁ = s₂ :=
begin 
  intro p, fapply sigma.sigma_eq, 
  exact p, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end  

@[hott]
def pair_eq {A B : Type _} : Π (c₁ c₂ : A × B), c₁.1 = c₂.1 -> c₁.2 = c₂.2 -> c₁ = c₂ :=
begin 
  intros c₁ c₂, 
  hinduction c₁ with c₁_1 c₁_2, hinduction c₂ with c₂_1 c₂_2, hsimp,
  intros q₁ q₂, apply ap011 pair q₁ q₂ 
end

@[hott]
def sigma2_eq' {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A}
  {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} : 
  Π (p : a₁ = a₂) (q : b₁ = b₂) (r : (ap011 C p q) ▸[id] c₁ = c₂), 
  dpair a₁ (dpair b₁ c₁) = ⟨a₂, ⟨b₂, c₂⟩⟩ :=
begin
  intros p q r, hinduction p, hinduction q, 
  fapply sigma.sigma_eq, refl, apply pathover_idp_of_eq, 
  fapply sigma.sigma_eq, refl, apply pathover_idp_of_eq, exact r
end  

@[hott]
def sigma.sigma_equiv_sigma_right_fst_eq : Π {A : Type _} {B C : A → Type _} 
  (Heqv : Π (a : A), B a ≃ C a) (ab : Σ (a : A), B a), 
  (sigma.sigma_equiv_sigma_right Heqv ab).1 = ab.1 :=
begin intros A B C Heqv ab, hinduction ab, exact idp end 

@[hott]
def sigma.sigma_eq_idp_idpo {A : Type _} {B : A -> Type _} {u : Σ (a : A), B a} :
  sigma.sigma_eq (@idp _ u.1) (@idpo _ _ u.1 u.2) = idp :=
begin 
  hinduction u, change sigma.dpair_eq_dpair _ _ = _, change apd011 _ _ _ = _, refl
end

/- The decode-encode technique for sums; it is contained in [types.sum] from the HoTT3 
   library, but this file does not compile. -/
@[hott, reducible, hsimp] 
def sum_code {A : Type.{u}} {B : Type.{v}} : A ⊎ B → A ⊎ B → Type (max u v) :=
  begin
    intros x y, induction x with a b; induction y with a' b',
    exact ulift.{(max u v) u} (a = a'), exact ulift empty,
    exact ulift empty, exact @ulift.{(max u v) v} (b = b')
  end   

@[hott] 
def sum_decode {A : Type.{u}} {B : Type.{v}} : 
  Π (z z' : A ⊎ B), sum_code z z' → z = z' :=
  begin
    intros z z', induction z with a b; induction z' with a' b',
    exact λ c, ap sum.inl (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, ap sum.inr (ulift.down c)
  end

@[hott] 
def sum_encode {A : Type.{u}} {B : Type.{v}} {z z' : A ⊎ B} (p : z = z') : sum_code z z' :=
  by induction p; induction z; exact ulift.up idp

@[hott] 
def empty_of_inl_eq_inr {A : Type.{u}} {B : Type.{v}} {a : A} {b : B} 
  (p : sum.inl a = sum.inr b) : empty :=
ulift.down (sum_encode p)

@[hott] 
def empty_of_inr_eq_inl {A : Type.{u}} {B : Type.{v}} {a : A} {b : B}
  (p : sum.inr b = sum.inl a) : empty := 
ulift.down (sum_encode p)

@[hott, instance] 
def decidable_eq_sum (A B : Type _)
    [HA : hott.decidable_eq A] [HB : hott.decidable_eq B] :
    hott.decidable_eq (A ⊎ B) :=
  begin
    intros v v', induction v with a b; induction v' with a' b',
    { hinduction HA a a',
      { exact decidable.inl (ap sum.inl a_1) },
      { apply decidable.inr, intro p, apply a_1, exact ulift.down (sum_encode p) }},
    { apply decidable.inr, intro p, apply empty_of_inl_eq_inr p },
    { apply decidable.inr, intro p, apply empty_of_inr_eq_inl p },
    { hinduction HB b b',
      { exact decidable.inl (ap sum.inr a) },
      { apply decidable.inr, intro p, apply a, exact ulift.down (sum_encode p) }},
  end

@[hott] 
def sum_eq_equiv {A : Type.{u}} {B : Type.{v}} {z z' : A ⊎ B} : (z = z') ≃ sum_code z z' :=
  begin
    fapply equiv.MK, apply sum_encode, apply sum_decode,
    { induction z with a b; induction z' with a' b';
       intro b; induction b with b; induction b; reflexivity },
    { intro p, induction p, induction z; refl  }
  end

@[hott] def sum.mem_cases {A : Type.{u}} {B : Type.{v}} (z : A ⊎ B) : 
  (Σ a, z = sum.inl a) ⊎ (Σ b, z = sum.inr b) :=
begin
  induction z with a b,
  exact sum.inl ⟨a, idp⟩, exact sum.inr ⟨b, idp⟩
end

/- Calculating with `dite`, from [types.sum] -/
@[hott] def dite_true {C : Type _} [H : decidable C] {A : Type _}
    {t : C → A} {e : ¬ C → A} (c : C) (H' : is_prop C) : dite C t e = t c :=
begin
  resetI, induction H with H H,
  exact ap t (is_prop.elim _ _),
  apply empty.elim, exact H c,
end

@[hott] def dite_false {C : Type _} [H : decidable C] {A : Type _}
  {t : C → A} {e : ¬ C → A} (c : ¬ C) : dite C t e = e c :=
begin
  resetI, induction H with H H,
  apply empty.elim, exact c H,
  exact ap e (is_prop.elim _ _),
end

/- The injectivity of a map of types is only useful if it also implies relations between
   equalities of objects of domain and codomain, in particular that `rfl` is mapped to 
   `rfl`. For sets, this is automatic and shown in [sets.basic]. We also show a criterion
   for injectivity using fibers. -/
@[hott]
class is_injective {A : Type u} {B : Type v} (f : B -> A) := 
  (eqv : forall b1 b2 : B, is_equiv (λ p : b1 = b2, ap f p))

@[hott]
def equiv_map_is_injective {A : Type u} {B₁ : Type v} {B₂ : Type w} (f₁ : B₁ -> A)
  (f₂ : B₂ -> A) : Π (eqv : B₁ ≃ B₂), f₁ = f₂ ∘ eqv.to_fun -> is_injective f₂ ->
  is_injective f₁ :=
begin 
  intros eqv f_eq f_inj₂, apply is_injective.mk, 
  intros b₁ c₁, fapply adjointify,
  { intro f₁_eq, apply eq_of_fn_eq_fn' eqv.to_fun, 
    apply (@is_injective.eqv _ _ f₂ f_inj₂ _ _).inv,
    exact (ap10 f_eq b₁)⁻¹ ⬝ f₁_eq ⬝ (ap10 f_eq c₁) },
  { intro q, rwr ap_fn_eq f_eq, apply con_inv_eq_of_eq_con, apply con_eq_of_eq_inv_con,
    rwr ap_compose f₂ eqv.to_fun, rwr ap_eq_of_fn_eq_fn', 
    change (λ p, ap f₂ p) _ = _,
    rwr (@is_injective.eqv _ _ f₂ f_inj₂ _ _).right_inv, rwr con.assoc },
  { intro p, hinduction p, rwr ap_idp, rwr con_idp, rwr con.left_inv, 
    have q : @is_equiv.inv _ _ _ (@is_injective.eqv _ _ f₂ f_inj₂ _ _) idp = 
                                                            @idp _ (eqv.to_fun b₁), from 
      begin apply inv_eq_of_eq, rwr ap_idp end,
    rwr q, change _ ⬝ _ ⬝ _ = _, rwr ap_idp, rwr con_idp, rwr con.left_inv }
end

@[hott]
def prop_fiber_is_inj {A : Type u} {B : Type v} (f : B -> A) : 
  (Π (a : A), is_prop (fiber f a)) -> is_injective f :=
begin
  intro is_prop_fib, 
  have H : Π {a : A} {fib₁ fib₂ : fiber f a} (q₁ q₂ : fib₁ = fib₂), q₁ = q₂, from 
    λ a fib₁ fib₂ q₁ q₂, @is_set.elim _ (@is_trunc_succ _ -1 (is_prop_fib a)) fib₁ fib₂ _ _, 
  apply is_injective.mk, intros b₁ b₂, fapply adjointify,
  { intro f_eq, 
    exact ap fiber.point (@is_prop.elim (fiber f (f b₂)) (is_prop_fib (f b₂)) 
                                        (fiber.mk b₁ f_eq) (fiber.mk b₂ idp)) },
  { intro p, let fib₁ := fiber.mk b₁ p, let fib₂ := fiber.mk b₂ (@idp _ (f b₂)), 
    have H' : (Σ(q : fib₁.point = fib₂.point), p = ap f q ⬝ idp), from 
      (fiber.fiber_eq_equiv _ _).to_fun (@is_prop.elim _ (is_prop_fib (f b₂)) 
                                           (fiber.mk b₁ p) (fiber.mk b₂ (@idp _ (f b₂)))),
    let r : p = ap f H'.1 := H'.2, apply concat _ r⁻¹,
    apply ap (ap f), apply concat _ (fiber.point_fiber_eq H'.1 H'.2),
    apply ap (ap fiber.point),
    rwr H (@is_prop.elim _ (is_prop_fib (f b₂))_ _) 
          (@fiber.fiber_eq _ _ _ _ (fiber.mk b₁ p) (fiber.mk b₂ idp) H'.1 H'.2) },
  { intro p, hinduction p, rwr ap_idp, rwr H (is_prop.elim _ _) idp } 
end

@[hott]
def inj_imp {A : Type u} {B : Type v} {f : B -> A} (inj : is_injective f) :  
  ∀ b1 b2 : B, f b1 = f b2 -> b1 = b2 :=
begin intros b1 b2, exact (is_injective.eqv f b1 b2).inv end  

@[hott]
def inj_idp {A : Type u} {B : Type v} {f : B -> A} [inj : is_injective f] :  
  ∀ b : B, inj_imp inj b b idp = idp :=
begin 
  intro b, 
  change @is_equiv.inv _ _ (λ p : b = b, ap f p) (is_injective.eqv f b b) 
                                                                (@idp _ (f b)) = idp, 
  have H : (λ p : b = b, ap f p) idp = idp, from rfl,
  rwr <- H, rwr @is_equiv.left_inv _ _ (λ p : b = b, ap f p) (is_injective.eqv f b b) (@idp _ b)
end 

/- Maps that are equivalences allow to exchange types of arguments in dependent 
   functions. -/
@[hott]
def equiv_arg_exchange {A : Type _} {B : Type _} {f : A -> B} (H : is_equiv f) 
  {C : B -> Type _} : (∀ a : A, C (f a)) -> (∀ b : B, C b) :=
begin intros g b, rwr <- is_equiv.right_inv f b, exact g (f⁻¹ᶠ b) end     

/- Some inequalities of natural numbers in the core are non-HoTT propositions, so procedures
   using them need to be rewritten.  -/
@[hott, hsimp] 
def list_nth_le {α : Type _} : Π (l : list α) (n), n < l.length → α
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := a
| (a :: l) (n+1) h := list_nth_le l n (le_of_succ_le_succ h)

@[hott]
def list_nth_le_eq {α : Type _} : Π {l : list α} {n : ℕ} (p p' : n < l.length),
  list_nth_le l n p = list_nth_le l n p' :=
assume l n p p', ap (list_nth_le l n) (is_prop.elim p p')

@[hott]
def list_nth_le_eq' {α : Type _} : Π {l : list α} {n m : ℕ} (p : n < l.length)
  (p' : m < l.length), n = m -> list_nth_le l n p = list_nth_le l m p' :=
begin intros l n m p p' q, hinduction q, exact list_nth_le_eq p p' end

/- Further facts on lists -/
@[hott, hsimp]
def list_map_size_eq {A B : Type _} (f : A -> B) (l : list A) : 
  list.length (list.map f l) = list.length l :=
begin hinduction l, refl, hsimp, rwr ih end  

@[hott]
def list_eq {A : Type _} {l₁ l₂ : list A} {a₁ a₂ : A} (ptl : l₁ = l₂) (phd : a₁ = a₂) :
  a₁ :: l₁ = a₂ :: l₂ := 
ap011 list.cons phd ptl

@[hott]
def list_length_append {A : Type _} (l₁ l₂ : list A) : 
  list.length (l₁ ++ l₂) = list.length l₁ + list.length l₂ :=
begin 
  hinduction l₁, hsimp, 
  change list.length (tl ++ l₂) + 1 = (list.length tl + 1) + list.length l₂, rwr ih,
  rwr nat.add_assoc, rwr nat.add_assoc, rwr nat.add_comm _ 1 
end

@[hott]
def list_append_el₁ {A : Type u} (l₁ l₂ : list A) (n : ℕ) (p : n < list.length l₁) :
  let q : n < list.length (l₁ ++ l₂) :=  
    nat.lt_of_lt_of_le (nat.lt_of_lt_of_le p (nat.le_add_right (list.length l₁) 
                    (list.length l₂))) (nat.le_of_eq (list_length_append l₁ l₂)⁻¹) in
  list_nth_le (l₁ ++ l₂) n q = list_nth_le l₁ n p :=
begin
  revert n p, hinduction l₁, 
    intros n p, hinduction nat.not_lt_zero n p,
    intro n, hinduction eq_zero_sum_eq_succ_pred n,  
      rwr val, intro p, exact idp,
      rwr val, intro p, hsimp, 
      let p' : (nat.pred n) < list.length tl := nat.le_of_succ_le_succ p, 
      apply square_diag_id (ih (nat.pred n) p'), 
      exact ap (list_nth_le _ _) (is_prop.elim _ _),
      exact ap (list_nth_le _ _) (is_prop.elim _ _)
end 

@[hott]
def list_append_el₂ {A : Type _} (l₁ l₂ : list A) (n : ℕ) (p : n < list.length l₂) :
  let q : list.length l₁ + n < list.length (l₁ ++ l₂) := 
    nat.lt_of_lt_of_le (nat.add_lt_add_left p (list.length l₁)) 
                                          (nat.le_of_eq (list_length_append l₁ l₂)⁻¹) in
  list_nth_le (l₁ ++ l₂) (list.length l₁ + n) q = list_nth_le l₂ n p :=
begin 
  hinduction l₁, 
    hsimp, apply list_nth_le_eq' _ _, exact nat.zero_add n, 
    hsimp, hsimp at ih, rwr <- ih, let q := nat.succ_add (list.length tl) n, 
    rwr apd011' (list_nth_le (hd :: (tl ++ l₂))) q, hsimp, rwr list_nth_le_eq
end 

/- Concatenating lists is associative. -/
@[hott]
def list_append_nil {A : Type _} : Π (l : list A), list.append l [] = l :=
  begin intro l, hinduction l, exact idp, exact ap (list.cons hd) ih end

@[hott]
def list_append_is_assoc {A : Type _} : Π (l₁ l₂ l₃ : list A), 
  list.append (list.append l₁ l₂) l₃ = list.append l₁ (list.append l₂ l₃)
| []       _  _  := idp
| _        [] _  := by rwr list_append_nil
| _        _  [] := by rwr list_append_nil; rwr list_append_nil
| (a₁::l₁) l₂ l₃  := begin change a₁::(list.append _ _) = a₁::(list.append _ _), 
                           rwr list_append_is_assoc end

/- Properties of reversing lists -/
@[hott]
def list_reverse_append {A : Type _} : Π (l₁ l₂ : list A),
  list.reverse_core l₁ l₂ = list.append (list.reverse l₁) l₂ :=
begin
  intro l₁, hinduction l₁, 
  { intro l₂, exact idp },
  { intro l₂, change list.reverse_core tl (hd :: l₂) = _, rwr ih (hd :: l₂), 
    change _ = list.append (list.reverse_core tl [hd]) _, rwr ih [hd],
    rwr list_append_is_assoc } 
end

/- Facts on fibers -/
@[hott]
def fiber_base_eq {A B : Type _} {f : A -> B} {b₁ b₂ : B} :
  fiber f b₁ -> b₁ = b₂ -> fiber f b₂ :=
λ fib₁ p, fiber.mk fib₁.point (fib₁.point_eq ⬝ p) 

@[hott]
def fiber_precomp {A B C : Type _} (f : A -> B) (g : B -> C) (c : C) : 
  fiber (g ∘ f) c -> fiber g c :=
begin intro fib_gf, fapply fiber.mk, exact f fib_gf.1, exact fib_gf.2 end

@[hott]
def fiber_ap_ap {A B : Type _} (f : A -> B) {b : B} {fib₁ fib₂ : fiber f b}
  (p : fib₁ = fib₂) : ap f (ap fiber.point p) = fib₁.2 ⬝ fib₂.2⁻¹ :=
begin 
  hinduction p, exact (con.right_inv fib₁.2)⁻¹
end

@[hott]
def fiber_comp {A B C : Type _} {f : A -> B} {g : B -> C} {c : C} 
  (fib_gf : fiber (g ∘ f) c) : Σ (fib_g : fiber g c), fiber f fib_g.point :=
dpair (fiber.mk (f fib_gf.point) fib_gf.point_eq) 
      (fiber.mk fib_gf.point idp)

@[hott]
def comp_fiber {A B C : Type _} {f : A -> B} {g : B -> C} {c : C} (fib_g : fiber g c) 
  (fib_f : fiber f fib_g.point) : fiber (g ∘ f) c :=
fiber.mk fib_f.point (ap g fib_f.point_eq ⬝ fib_g.point_eq)  

@[hott]
def comp_fib_eq {A B C : Type _} (f : A -> B) (g : B -> C) {c : C} 
  {fib_g₁ fib_g₂ : fiber g c} {fib_f₁ : fiber f fib_g₁.point}
  {fib_f₂ : fiber f fib_g₂.point} (p : fib_g₁ = fib_g₂) (q₁ : fib_f₁.point = fib_f₂.point)
  (q₂ : fib_f₁.point_eq ⬝ ap fiber.point p = ap f q₁ ⬝ fib_f₂.point_eq) : 
  comp_fiber fib_g₁ fib_f₁ = comp_fiber fib_g₂ fib_f₂ :=
begin
  hinduction p, hinduction fib_f₁ with a₁ f_eq₁, hinduction fib_f₂ with a₂ f_eq₂, 
  change a₁ = a₂ at q₁, hinduction q₁, change f_eq₁ = idp ⬝ f_eq₂ at q₂, 
  fapply fiber.fiber_eq,
  { exact idp },
  { apply (λ q, q ⬝ (idp_con (ap g f_eq₂ ⬝ fib_g₁.point_eq))⁻¹), 
    apply ap (λ q, ap g q ⬝ fib_g₁.point_eq), exact q₂ ⬝ (idp_con _) }
end

@[hott]
def fib_comp_fib_eq {A B C : Type _} {f : A -> B} {g : B -> C} {c : C} 
  (fib_gf : fiber (g ∘ f) c) : 
  fib_gf = comp_fiber (fiber.mk (f fib_gf.1) fib_gf.2) (fiber.mk fib_gf.1 idp) :=
begin 
  hinduction fib_gf with a gf_eq, change _ = fiber.mk a (idp ⬝ gf_eq), rwr idp_con
end 

@[hott]
def eq_equiv_fn_eq_of_equiv_idp {A : Type u} {B : Type v} (f : A ≃ B) (a : A) :
  equiv.eq_equiv_fn_eq_of_equiv f a a idp = idp := idp  

@[hott]
def sigma_eq_equiv_idp {A : Type _} {B : A → Type _} (u : Σ (a : A), B a) :
  sigma.sigma_eq_equiv u u idp = ⟨idp, idpo⟩ := idp

@[hott]
def sigma_equiv_sigma_right_red {A : Type _} {B : A → Type _} {B' : A → Type _}
  (f : (Π (a : A), B a ≃ B' a)) : (sigma.sigma_equiv_sigma_right f).to_fun =
  sigma.sigma_functor id (λ a, (f a).to_fun) := idp 

@[hott]
def sigma_equiv_sigma_right_idp {A B : Type _} {f : A -> B} {a : A} {b : B}
  {q : f a = b} : sigma.sigma_equiv_sigma_right (λ (p : a = a),
                   @eq_pathover_equiv_Fl A B a a b f p q q) ⟨idp, idpo⟩ = 
                   ⟨idp, (idp_con q)⁻¹⟩ := 
begin 
  change (sigma.sigma_equiv_sigma_right (λ (p : a = a),
                   @eq_pathover_equiv_Fl A B a a b f p q q)).to_fun _ = _,
  rwr sigma_equiv_sigma_right_red, 
  change dpair idp _ = _, fapply sigma.sigma_eq, exact idp,
  apply pathover_of_tr_eq, rwr idp_tr,
  change (pathover_idp _ _ _ ⬝e equiv_eq_closed_right _ (eq.inverse (idp_con q))).to_fun 
                                                                  idpo = (idp_con q)⁻¹, 
  rwr equiv.to_fun_trans,
  change (equiv_eq_closed_right q (idp_con q)⁻¹).to_fun idp = _,
  change idp ⬝ _ = _, rwr idp_con (idp_con q)⁻¹  
end

@[hott]
def fiber_eq_idp {A B : Type _} (f : A -> B) {b : B} (fib : fiber f b) :
  fiber.fiber_eq (@idp _ fib.1) (idp_con fib.2)⁻¹ = idp :=
begin 
  change (_ ⬝e (_ ⬝e _)).to_fun⁻¹ᶠ _ = _, 
  rwr equiv.to_inv_trans, rwr equiv.to_inv_trans, 
  apply equiv.to_inv_eq_of_eq (equiv.eq_equiv_fn_eq_of_equiv _ _ _), 
  rwr eq_equiv_fn_eq_of_equiv_idp, 
  apply equiv.to_inv_eq_of_eq (sigma.sigma_eq_equiv _ _),
  rwr sigma_eq_equiv_idp, 
  apply equiv.to_inv_eq_of_eq (sigma.sigma_equiv_sigma_right _), 
  rwr sigma_equiv_sigma_right_idp 
end 

@[hott]
def comp_fib_eq_idp {A B C : Type _} (f : A -> B) (g : B -> C) {c : C} 
  {fib_g : fiber g c} {fib_f : fiber f fib_g.point} : 
  comp_fib_eq f g (@idp _ fib_g) (@idp _ fib_f.point) (idp_con fib_f.point_eq)⁻¹ = idp :=
begin
  hinduction fib_f with a f_eq, change fiber.fiber_eq idp _ = idp,
  change fiber.fiber_eq idp (_ ⬝ _) = idp, rwr con.left_inv, 
  apply λ p, p ⬝ fiber_eq_idp (g ∘ f) _, 
  fapply apd011 fiber.fiber_eq, exact idp, apply pathover_of_tr_eq, rwr idp_tr,
  apply con_inv_eq_of_eq_con, change _ = (idp_con (ap g f_eq ⬝ fib_g.point_eq))⁻¹ ⬝ _, 
  rwr con.left_inv
end

@[hott]
def comp_fib_eq_idp_idp {A B C : Type _} {f : A -> B} {g : B -> C} {c : C} 
  (fib_g : fiber g c) (fib_f : fiber f fib_g.point) 
  {r : fib_f.point_eq ⬝ ap fiber.point idp = ap f idp ⬝ fib_f.point_eq} : 
  r = (idp_con fib_f.point_eq)⁻¹ ->
  comp_fib_eq f g (@idp _ fib_g) (@idp _ fib_f.point) r = idp :=
begin intro s, rwr s, exact comp_fib_eq_idp f g end

/- We use Egbert Rijke's insight that the main tool to deal with identity types in 
   HoTT is the Structure Identity Principle for Σ-types [Rijke-Book, Thm.11.6.2]. 
   It is the dependent version of the Fundamental Theorem of identity types
   [Thm.11.2.2] which characterizes the identity types of a type by identity
   systems which are type families with the same inductive properties as identity: 
   The fibers of such a type family are equivalent to the identity types if the 
   total space of the type family is contractible. See also [HoTT-Book, Ch.5.8]. -/
@[hott]
structure ppred {A : Type _} (a₀ : A) := 
  (fam : A -> Type _)
  (base : fam a₀)

attribute [reducible] ppred.fam

@[hott]
def id_ppred {A : Type _} (a₀ : A) : ppred a₀ :=
  @ppred.mk A a₀ (λ a : A, a₀ = a) (idpath a₀) 

@[hott] 
structure ppmap {A : Type _} {a₀ : A} (R S : ppred a₀) := 
  (fam_map : Π (a : A), R.fam a -> S.fam a)
  (base_map : fam_map a₀ R.base = S.base) 

@[hott]
def is_id_system {A : Type _} {a₀ : A} (R : ppred a₀) := 
  Π (D : Π (a : A), R.fam a -> Type _) (d₀ : D a₀ R.base),
      Σ (f : Π (a : A) (r : R.fam a), D a r), (f a₀ R.base = d₀) 

@[hott]
def id_type_fam_is_id_sys {A : Type _} {a₀ : A} : is_id_system (id_ppred a₀) :=
begin 
  intros D d, fapply dpair, 
  { intros a p, hinduction p, exact d },
  { refl }
end

@[hott]
def is_prop_is_id_sys {A : Type _} {a₀ : A} (R : ppred a₀) :
  is_prop (is_id_system R) :=
begin
  fapply is_prop.mk, intros is_id_sys_R is_id_sys_R',
  fapply eq_of_homotopy2, intros D d, 
  let D_eq := λ a r, (is_id_sys_R D d).1 a r = (is_id_sys_R' D d).1 a r,
  let d_eq := (is_id_sys_R D d).2 ⬝ (is_id_sys_R' D d).2⁻¹,                                     
  fapply sigma.sigma_eq, 
  { fapply eq_of_homotopy2, intros a r,
    exact (is_id_sys_R D_eq d_eq).1 a r },
  { apply @po_of_po_apd100 _ _ D _ _ (λ d' : D a₀ R.2, d' = d), 
    let H : (is_id_sys_R D d).1 ~2 (is_id_sys_R' D d).1 
          := λ (a : A) (r : R.fam a), (is_id_sys_R D_eq d_eq).1 a r,
    change _ =[apd100 (eq_of_homotopy2 H) a₀ R.base] _,
    rwr apd100_eq_of_hty2_inv H a₀ R.base, apply eq_con_po_eq,
    have q : (is_id_sys_R D_eq d_eq).1 a₀ R.base = d_eq, from
      (is_id_sys_R D_eq d_eq).2,      
    have p : H a₀ R.base = d_eq, by 
      change (is_id_sys_R _ _).1 a₀ R.base = _; rwr q,
    rwr p, hsimp }
end  

@[hott]
structure id_system {A : Type _} (a₀ : A) := 
  (ppred : ppred a₀) 
  (is_id_sys : is_id_system ppred)

/- We split up the implications between the properties of the Fundamental 
   Theorem of Identity as in the proof of [Rijke-Book, Thm.11.2.2].
   The properties are all propositions, hence equivalent, but this 
   seems not needed in the applications. -/
@[hott]
def tot_space_contr_id_sys {A : Type _} {a₀ : A} (R : ppred a₀) : 
  is_contr (Σ (a : A), R.fam a) -> is_id_system R :=
begin 
  intros contr D d, 
  let D' : (Σ (a : A), R.fam a) -> Type _ := λ (ar : Σ (a : A), R.fam a), D ar.1 ar.2,
  have p : Π (u : Σ (a : A), R.fam a), u = ⟨a₀, R.base⟩, from 
    assume u, @eq_of_is_contr _ contr _ _,
  have q : p ⟨a₀, R.base⟩ = idp, from @prop_eq_of_is_contr _ contr _ _ _ _,  
  fapply dpair, 
  { exact λ (a : A) (r : R.fam a), (p ⟨a, r⟩)⁻¹ ▸[D'] d },
  { apply inv_tr_eq_of_eq_tr, rwr q }
end  

@[hott]
def id_sys_tot_space_contr {A : Type _} {a₀ : A} (R : ppred a₀) : 
  is_id_system R -> is_contr (Σ (a : A), R.1 a) :=
begin 
  intro is_id_sys_R, fapply is_contr.mk,
  { exact ⟨a₀, R.base⟩ },
  { let D : Π (a : A), R.fam a -> Type _ := λ a r, 
                            @dpair A R.fam a₀ R.base = ⟨a, r⟩, 
    intro dp, hinduction dp with a r, 
    exact (is_id_sys_R D idp).1 a r }
end

/- We need some facts on families of equivalences, see [Rijke-Book, 11.1]. -/
@[hott] --[Rijke-Book, Thm.11.1.3.(i)=>(ii)] = [HoTT-Book, Thm.4.7.7]
def fam_eqv_tot_map_eqv {A : Type _} {B C : A -> Type _} 
  (f : Π a : A, B a -> C a) : 
  (Π a : A, is_equiv (f a)) -> is_equiv (sigma.total f) :=
λ fib_eqv, @is_equiv_total_of_is_fiberwise_equiv _ _ _ f fib_eqv

@[hott] --[Rijke-Book, Thm.11.1.3.(ii)=>(i)] = [HoTT-Book, Thm.4.7.7]
def tot_map_eqv_fam_eqv {A : Type _} {B C : A -> Type _} 
  (f : Π a : A, B a -> C a) : 
  is_equiv (sigma.total f) -> (Π a : A, is_equiv (f a)) :=
λ tot_eqv, @is_fiberwise_equiv_of_is_equiv_total _ _ _ f tot_eqv 

/- Now we can show the second pair of implications in [Rijke-Book, Thm.11.2.2]. 
   In particular, we can apply them to the canonical maps from the identity
   pointed predicate to arbitrary pointed predicates. -/
@[hott, reducible]
def can_ppmap {A : Type _} {a₀ : A} (R : ppred a₀) : 
  ppmap (id_ppred a₀) R :=
⟨λ (a : A) (p : a₀ = a), p ▸[λ a : A, R.fam a] R.base, idp⟩  

@[hott]
def ppmap_id_eqv_tot_space_contr {A : Type _} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), (Π (a : A), is_equiv (f.fam_map a)) ->
  is_contr (Σ (a : A), R.fam a) := 
begin
  intros f f_eqv, 
  have F : (Σ (a : A), a₀ = a) ≃ (Σ (a : A), R.fam a), from
    equiv.mk (sigma.total f.fam_map) (fam_eqv_tot_map_eqv f.fam_map f_eqv),
  exact is_trunc_equiv_closed -2 F (is_contr_tot_peq a₀)  
end

@[hott]
def ppmap_id_eqv_tot_space_contr' {A : Type _} {a₀ : A} (R : ppred a₀) : 
  Π eqv_fam : Π (a : A), (a₀ = a) ≃ (R.fam a), eqv_fam a₀ idp = R.base -> 
    is_contr (Σ (a : A), R.fam a) := 
begin
  intros eqv_fam base_eq,
  fapply ppmap_id_eqv_tot_space_contr R, 
  { fapply ppmap.mk,
    { intro a, exact eqv_fam a },
    { exact base_eq } },
  { intro a, exact (eqv_fam a).to_is_equiv }
end

@[hott]
def tot_space_contr_ppmap_id_eqv {A : Type _} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), is_contr (Σ (a : A), R.fam a) -> 
  Π (a : A), is_equiv (f.fam_map a) := 
begin
  intros f contr_tot_R, apply tot_map_eqv_fam_eqv, 
  apply @is_equiv_of_is_contr _ _ (is_contr_tot_peq a₀) contr_tot_R
end

@[hott]
def tot_space_contr_ppmap_id_eqv' {A : Type _} {a₀ : A} (R : ppred a₀) : 
  (ppmap (id_ppred a₀) R) -> is_contr (Σ (a : A), R.fam a) -> 
  Π (a : A), (a₀ = a) ≃ (R.fam a) :=
begin
  intros f contr_tot_R, intro a, 
  exact equiv.mk (f.fam_map a) (tot_space_contr_ppmap_id_eqv R f contr_tot_R a)
end

/- In HoTT3, types with structures are usually defined as `structure`, 
   not Σ-types. Therefore, we need to provide equivalences of structures 
   with Σ-types before we can apply the Structure Identity Principle 
   on types with structure. The proof follows that of [Rijke-Book, Thm.11.6.2], 
   splitting up the Fundamental Identity Theorem for Σ-Types into 
   checks for pointed predicates over objects of the Σ-type with 
   fixed first component and over objects of the first component. -/
@[hott]
structure dep_ppred {A : Type _} (a₀ : A) {B : A -> Type _} (b₀ : B a₀) :=
  (ppred_fst : ppred a₀)
  (dep_fam : Π (a : A), B a -> ppred_fst.fam a -> Type _) 
  (dep_base : dep_fam a₀ b₀ ppred_fst.base) 

attribute [reducible] dep_ppred.dep_fam

@[hott]
def is_dep_id_system {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) := 
is_id_system (@ppred.mk _ b₀ (λ (b : B a₀), 
               R.dep_fam a₀ b R.ppred_fst.base) R.dep_base)  

@[hott]
structure dep_id_system {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} :=
(dep_ppred : dep_ppred a₀ b₀)
(id_sys_fst : is_id_system dep_ppred.ppred_fst)  
(is_dep_id_sys : is_dep_id_system dep_ppred)

/- We only need to show one equivalence between characterizations of 
   the identities in Σ-Types and identities of objects of the Σ-type 
   with fixed first component: the contractibility of the total space
   of the pairs with fixed first component and the contractibility of 
   the total space of the associated pointed predicate on the Σ-type. 
   
   The other equivalences are consequences of the equivalences in the 
   Fundamental Identity Theorem: We just include that dependent 
   identity systems give rise to identity systems on the Σ-type and
   vice versa, and state the criterion to produce equivalences from
   contractibility. -/
@[hott]
def struct_id_eqv₁ {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) :
  (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base) ≃
              (Σ (dp : Σ (a : A), R.ppred_fst.fam a), 
                 Σ (b : B dp.1), R.dep_fam dp.1 b dp.2) :=
begin
  let ceq : @center _ (id_sys_tot_space_contr R.ppred_fst id_sys_fst) =
             ⟨a₀, R.ppred_fst.base⟩ := idp,
  let ppred_fst_eq : Π (ac : Σ (a : A), R.ppred_fst.fam a),
        ac = ⟨a₀, R.ppred_fst.base⟩, by intro ac; 
    exact @eq_of_is_contr _ (id_sys_tot_space_contr R.ppred_fst 
                             id_sys_fst) _ _,
  have p : ppred_fst_eq ⟨a₀, R.ppred_fst.base⟩ = idp, from 
    @prop_eq_of_is_contr _ (id_sys_tot_space_contr R.ppred_fst 
                            id_sys_fst) _ _ _ _,                         
  let f := λ (ac : Σ (a : A), R.ppred_fst.fam a) 
             (bd : Σ (b : B ac.1), R.dep_fam ac.1 b ac.2),
             (ppred_fst_eq ac) ▸[λ (ac : Σ (a : A), R.ppred_fst.fam a), 
                        (Σ (b : B ac.1), R.dep_fam ac.1 b ac.2)] bd,              
  fapply equiv.mk,
    { intro dpB, exact ⟨⟨a₀, R.ppred_fst.base⟩, dpB⟩ },
    { fapply adjointify, 
      { intro dpR1, exact f dpR1.1 dpR1.2 },
      { intro ptR, hinduction ptR with ptd ptB, 
        hinduction ptd with a ca, 
        hinduction ptB with b bR, hsimp, fapply sigma.sigma_eq,
        exact (ppred_fst_eq ⟨a, ca⟩)⁻¹, hsimp, 
        apply pathover_of_tr_eq, apply inv_tr_eq_of_eq_tr, refl }, 
      { intro ptB, hinduction ptB with b bR, hsimp, 
        change (ppred_fst_eq ⟨a₀, R.ppred_fst.base⟩) ▸ _ = _, 
        rwr p } }
end

@[hott]
def struct_id_eqv₂ {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) :
  (Σ (dp : Σ (a : A), R.ppred_fst.fam a), 
                 Σ (y : B dp.1), R.dep_fam dp.1 y dp.2) ≃
           (Σ (dp : Σ (a : A), B a), 
            Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) :=
begin
  fapply equiv.mk,
  { intro tup, exact ⟨⟨tup.1.1, tup.2.1⟩, ⟨tup.1.2, tup.2.2⟩⟩ },
  { fapply adjointify, 
    { intro tup, exact ⟨⟨tup.1.1, tup.2.1⟩, ⟨tup.1.2, tup.2.2⟩⟩ },
    { intro tup, hsimp, hinduction tup with tup₁ tup₂, 
      hinduction tup₁ with a c, hinduction tup₂ with b d, hsimp },
    { intro tup, hsimp, hinduction tup with tup₁ tup₂, 
      hinduction tup₁ with a b, hinduction tup₂ with c d, hsimp } }
end

@[hott]
def struct_id_dep_contr_to_contr {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) : 
  is_contr (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base) ->
  is_contr (Σ (dp : Σ (a : A), B a), 
            Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) :=
begin
  intro contr₁, fapply @is_trunc_equiv_closed (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base), 
  exact (struct_id_eqv₁ R id_sys_fst) ⬝e (struct_id_eqv₂ R), 
  exact contr₁
end  

@[hott]
def struct_id_contr_to_dep_contr {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) : 
  is_contr (Σ (dp : Σ (a : A), B a), 
            Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) ->
  is_contr (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base)
  :=
begin
  intro contr₂, 
  exact is_trunc_equiv_closed_rev -2 ((struct_id_eqv₁ R id_sys_fst) ⬝e 
                                  (struct_id_eqv₂ R)) contr₂
end 

@[hott]
def struct_id_dep_id_sys_eqv {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) : (is_dep_id_system R) ↔
  (is_id_system (@ppred.mk (Σ (a : A), B a) ⟨a₀, b₀⟩ 
    (λ dp, Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) 
    ⟨R.ppred_fst.base, R.dep_base⟩)) :=
begin
  apply pair, 
  { intro dep_id_sys, apply tot_space_contr_id_sys,
    apply struct_id_dep_contr_to_contr R id_sys_fst, 
    exact id_sys_tot_space_contr (@ppred.mk _ b₀ (λ (b : B a₀), 
      R.dep_fam a₀ b R.ppred_fst.base) R.dep_base) dep_id_sys },
  { intro id_sys, apply tot_space_contr_id_sys, 
    apply struct_id_contr_to_dep_contr R id_sys_fst, 
    exact id_sys_tot_space_contr _ id_sys }
end    

@[hott,reducible] --[GEVE]
def struct_id_char_of_contr {A : Type _} {a₀ : A} {B : A -> Type _} 
  (b₀ : B a₀) (D : dep_ppred a₀ b₀) : 
  is_contr (Σ (a : A), D.ppred_fst.fam a) -> 
  is_contr (Σ (b : B a₀), D.dep_fam a₀ b D.ppred_fst.base) ->
  Π (ab : Σ (a : A), B a), (dpair a₀ b₀ = ab) ≃ 
       Σ (c : D.ppred_fst.fam ab.1), D.dep_fam ab.1 ab.2 c :=
begin
  intros is_contr_fst is_contr_dep ab, fapply equiv.mk,
  let R := @ppred.mk _ (dpair a₀ b₀) 
              (λ ab, Σ (c : D.ppred_fst.fam ab.fst), 
                            D.dep_fam ab.fst ab.snd c) 
              ⟨D.ppred_fst.base, D.dep_base⟩,
  { exact (can_ppmap R).fam_map ab },
  { apply tot_space_contr_ppmap_id_eqv, hsimp,
    have id_sys_fst : is_id_system D.ppred_fst, from 
      tot_space_contr_id_sys D.ppred_fst is_contr_fst, 
    apply struct_id_dep_contr_to_contr D id_sys_fst is_contr_dep }
end 

@[hott,reducible]
def struct_id_char_of_contr_idp {A : Type _} {a₀ : A} {B : A -> Type _} 
  (b₀ : B a₀) (D : dep_ppred a₀ b₀)  
  (contr : is_contr (Σ (a : A), D.ppred_fst.fam a)) 
  (contr_dep : is_contr (Σ (b : B a₀), D.dep_fam a₀ b D.ppred_fst.base)) :
  struct_id_char_of_contr b₀ D contr contr_dep ⟨a₀, b₀⟩ idp = 
  ⟨D.ppred_fst.base, D.dep_base⟩ :=
begin 
  change ((can_ppmap (@ppred.mk _ (dpair a₀ b₀) 
              (λ ab, Σ (c : D.ppred_fst.fam ab.fst), 
                            D.dep_fam ab.fst ab.snd c) 
       ⟨D.ppred_fst.base, D.dep_base⟩)).fam_map ⟨a₀, b₀⟩) idp = _, 
  hsimp 
end

/- A useful fact when we want to apply characterizations of identity types -/
@[hott]
def obj_char_id_eq {A : Type _} {a₀ : A} {B : A -> Type _}
  (f : Π {a : A}, (a₀ = a) ≃ B a) : 
  Π (a : A) (Ha : B a), @f a₀ (refl a₀) =[(@f a)⁻¹ᶠ Ha] Ha :=
begin
  intros a Ha, 
  have Hp : Π (p : a₀ = a), @f a₀ (refl a₀) =[p] @f a p, by
    intro p; hinduction p; exact idpo, 
  have HHa : Ha = @f a ((@f a)⁻¹ᶠ Ha), by 
    rwr is_equiv.right_inv (@f a) Ha,
  exact concato_eq (Hp ((@f a)⁻¹ᶠ Ha)) HHa⁻¹
end  

/- We need a set-type `Two` with two objects to deduce propositional resizing from LEM.
   To construct it we also need `Zero` and `One`. 

   [Zero] and [One] are equivalent to [true] and [false] in [prop_logic], but
   we want to use them without logical connotations. -/
@[hott]  --[GEVE]
inductive Zero : Type _

@[hott]
def eq_Zero : forall f₁ f₂ : Zero, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance] --[GEVE]
def Zero_is_prop : is_prop Zero :=
  is_prop.mk eq_Zero 

@[hott]
def Zero_Set : Set :=
  Set.mk Zero (is_trunc_succ Zero -1)

@[hott, instance]
def is_prop_Zero_equiv (A : Type _) : is_prop (Zero ≃ A) :=
begin 
  apply is_prop.mk, intros eqv₁ eqv₂,
  have H : is_prop A, from is_trunc_equiv_closed -1 eqv₁ Zero_is_prop, 
  hinduction eqv₁ with f₁ is_eqv₁, hinduction eqv₂ with f₂ is_eqv₂,
  fapply apd011 equiv.mk, 
  { apply eq_of_homotopy, intro o, exact @is_prop.elim _ H _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]  --[GEVE]
inductive One : Type _  
| star : One

@[hott] --[GEVE]
def eq_One : forall t₁ t₂ : One, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl One.star),
end 

@[hott, instance]
def One_dec_eq : decidable_eq One := assume t₁ t₂, decidable.inl (eq_One t₁ t₂) 

@[hott, instance] --[GEVE]
def One_is_prop : is_prop One :=
  is_prop.mk eq_One

@[hott]
def One_Set : Set :=
  Set.mk One (is_trunc_succ One -1)

@[hott, instance]
def is_prop_One_equiv (A : Type _) : is_prop (One ≃ A) :=
begin 
  apply is_prop.mk, intros eqv₁ eqv₂,
  have H : is_prop A, from is_trunc_equiv_closed -1 eqv₁ One_is_prop, 
  hinduction eqv₁ with f₁ is_eqv₁, hinduction eqv₂ with f₂ is_eqv₂,
  fapply apd011 equiv.mk, 
  { apply eq_of_homotopy, intro o, exact @is_prop.elim _ H _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]
inductive Two : Type _  --[GEVE]
| zero : Two 
| one : Two 

/- We prove that [Two] is a set using the Fundamental Identity Theorem, 
   following [Rijke-Book, 11.3]. This is a streamlined version of the
   encode-decode method presented in [HoTT-book, Sec.2.13], getting rid 
   of the decoding. -/
@[hott, hsimp]
def code_Two : Two -> Two -> Type _ :=
begin
  intros t₁ t₂, 
  hinduction t₁,
    hinduction t₂, exact One, exact Zero,
    hinduction t₂, exact Zero, exact One,
end  

@[hott, instance]
def code_Two_is_prop : Π t₁ t₂ : Two, is_prop (code_Two t₁ t₂) :=
begin
  intros t₁ t₂, hinduction t₁, 
  hinduction t₂, exact One_is_prop, exact Zero_is_prop,
  hinduction t₂, exact Zero_is_prop, exact One_is_prop,
end

@[hott]
def refl_Two : Π t : Two, code_Two t t := 
begin intro t; hinduction t; exact One.star; exact One.star end

@[hott, hsimp]
def encode_Two : Π t₁ t₂ : Two, (t₁ = t₂) -> code_Two t₁ t₂ :=
  assume t₁ t₂ eq, eq ▸[λ t : Two, code_Two t₁ t] (refl_Two t₁)

@[hott] --[GEVE]
def Two_eq_equiv_code : ∀ t₁ t₂ : Two, (t₁ = t₂) ≃ code_Two t₁ t₂ := 
begin 
  intros t₁ t₂, 
  let R := ppred.mk (λ t₂ : Two, code_Two t₁ t₂) (refl_Two t₁),
  let f := @ppmap.mk _ _ (id_ppred t₁) R 
                    (λ t₂ : Two, encode_Two t₁ t₂) idp, 
  fapply equiv.mk, exact encode_Two t₁ t₂,
  apply tot_space_contr_ppmap_id_eqv R f, fapply is_contr.mk,
  exact ⟨t₁, refl_Two t₁⟩, intro tp, hinduction tp with t ct, 
  hinduction t₁, 
    hinduction t, hinduction ct; refl, exact Zero.rec _ ct,  
    hinduction t, exact Zero.rec _ ct, hinduction ct; refl
  end  

@[hott, instance] --[GEVE]
def Two_eq_is_prop : Π (t₁ t₂ : Two.{u}), is_prop (t₁ = t₂) :=
  λ t₁ t₂ : Two, is_trunc_equiv_closed_rev.{u u} 
          -1 (Two_eq_equiv_code t₁ t₂) (code_Two_is_prop t₁ t₂)

@[hott, instance]
def Two_is_set : is_set Two :=
  is_trunc_succ_intro (λ t₁ t₂, Two_eq_is_prop t₁ t₂)

@[hott]
def Two_Set : Set :=
  Set.mk Two Two_is_set  

@[hott]
def Two_is_decidable : ∀ t₁ t₂ : Two, (t₁ = t₂) ⊎ ¬ (t₁ = t₂) :=
begin 
  intros t₁ t₂, 
  induction t₁, 
    induction t₂, exact sum.inl rfl, 
                  apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
    induction t₂, apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
                  exact sum.inl rfl,              
end    

end hott