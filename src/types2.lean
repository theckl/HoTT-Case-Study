import init2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc  

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

@[hott] def sum.swap {A : Type.{u}} : A ⊎ A -> A ⊎ A :=
  begin intro s, hinduction s with a a, exact sum.inr a, exact sum.inl a end

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
  intros b₁ c₁, fapply is_equiv.adjointify,
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

@[hott]
def fiber_homotopy_equiv {A B : Type _} {f f' : A -> B} :
  (f ~ f') -> Π (b : B), fiber f b ≃ fiber f' b :=
begin
  intros H b, fapply equiv.mk,
  { intro fib, hinduction fib with a f_eq, exact fiber.mk a ((H a)⁻¹ ⬝ f_eq) },
  { fapply adjointify,
    { intro fib', hinduction fib' with a f'_eq, exact fiber.mk a (H a ⬝ f'_eq) },
    { intro fib', hinduction fib' with a f'_eq, fapply fiber.fiber_eq,
      exact idp, rwr ap_idp, rwr idp_con, change (H a)⁻¹ ⬝ (H a ⬝ f'_eq) = f'_eq, 
      rwr <- con.assoc, rwr con.left_inv, exact idp_con _ },
    { intro fib, hinduction fib with a f_eq, fapply fiber.fiber_eq,
      exact idp, rwr ap_idp, rwr idp_con, change (H a) ⬝ ((H a)⁻¹ ⬝ f_eq) = f_eq, 
      rwr <- con.assoc, rwr con.right_inv, exact idp_con _ } }
end  

end hott