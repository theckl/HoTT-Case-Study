import sets.product algebra.monoid.submonoid  

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets subset hott.relation categories.sets

namespace algebra

/- We characterize and construct products of two monoids using products of the 
   underlying sets. This implies and is implied by the standard universal property. -/
@[hott]  --[GEVE]
structure is_monoid_product (M N P : Monoid) :=
  (set_prod : is_product (Monoid_to_Set_functor.obj M) 
                      (Monoid_to_Set_functor.obj N) (Monoid_to_Set_functor.obj P))
  (fst_hom : Σ (pr₁ : P ⟶ M), Monoid_to_Set_functor.map pr₁ = set_prod.fst)
  (snd_hom : Σ (pr₂ : P ⟶ N), Monoid_to_Set_functor.map pr₂ = set_prod.snd)

@[hott]  --[GEVE]
def product_monoid (M N : Monoid) : Monoid :=
begin
  fapply Monoid.mk (Monoid_to_Set_functor.obj M × Monoid_to_Set_functor.obj N),
  fapply monoid.mk,
  { apply_instance },
  { exact λ mn₁ mn₂, ⟨mn₁.1 * mn₂.1, mn₁.2 * mn₂.2⟩ },
  { intros mn₁ mn₂ mn₃, fapply pair_eq, apply monoid.mul_assoc, apply monoid.mul_assoc },
  { exact ⟨M.struct.one, N.struct.one⟩ },
  { intro mn, fapply pair_eq, apply monoid.one_mul, apply monoid.one_mul },
  { intro mn, fapply pair_eq, apply monoid.mul_one, apply monoid.mul_one }
end

@[hott]  --[GEVE]
def product_monoid_is_product (M N : Monoid) : is_monoid_product M N (product_monoid M N) :=
begin
  fapply is_monoid_product.mk, 
  { exact type_product_is_product _ _ },
  { fapply dpair, 
    { fapply monoid_hom.mk, 
      { exact prod.fst },
      { fapply monoid_hom_str.mk,
        { intros mn₁ mn₂, exact idp },
        { exact idp } } }, 
    { exact idp } },
  { fapply dpair, 
    { fapply monoid_hom.mk, 
      { exact prod.snd },
      { fapply monoid_hom_str.mk,
        { intros mn₁ mn₂, exact idp },
        { exact idp } } }, 
    { exact idp } }
end

@[hott]  --[GEVE]
structure is_univ_monoid_product (M N P : Monoid) :=
  (fst : P ⟶ M)
  (snd : P ⟶ N)
  (factors : Π {Q : Monoid} (q_M : Q ⟶ M) (q_N : Q ⟶ N), Σ (q_P : Q ⟶ P), 
               (q_P ≫ fst = q_M) × (q_P ≫ snd = q_N))
  (unique : Π {Q : Monoid} (q_P q_P' : Q ⟶ P),
               q_P ≫ fst = q_P' ≫ fst -> q_P ≫ snd = q_P' ≫ snd -> q_P = q_P')

@[hott]
def monoid_to_univ_prod_hom {M N P : Monoid} (is_prod : is_monoid_product M N P) :
  Π {Q : Monoid} (q_M : Q ⟶ M) (q_N : Q ⟶ N), Q ⟶ P :=
begin
  let is_set_prod' := (equiv_char_of_products _ _ _).1 is_prod.set_prod,
  intros Q q_M q_N, fapply monoid_hom.mk, 
  { fapply (is_set_prod'.factors _ _).1,
    exact Monoid_to_Set_functor.map q_M, exact Monoid_to_Set_functor.map q_N },
  { fapply monoid_hom_str.mk,
    {intros q₁ q₂, fapply is_prod.set_prod.pair_unique,
      { change is_set_prod'.fst _ = _,
        rwr ((is_set_prod'.factors _ _).2 (q₁ * q₂)).1,
        rwr <- is_prod.fst_hom.2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr ap10 is_prod.fst_hom.2, rwr ap10 is_prod.fst_hom.2,
        change _ = is_set_prod'.fst _ * is_set_prod'.fst _, 
        rwr ((is_set_prod'.factors _ _).2 q₁).1, 
        rwr ((is_set_prod'.factors _ _).2 q₂).1 },
      { change is_set_prod'.snd _ = _,
        rwr ((is_set_prod'.factors _ _).2 (q₁ * q₂)).2,
        rwr <- is_prod.snd_hom.2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr ap10 is_prod.snd_hom.2, rwr ap10 is_prod.snd_hom.2,
        change _ = is_set_prod'.snd _ * is_set_prod'.snd _, 
        rwr ((is_set_prod'.factors _ _).2 q₁).2, 
        rwr ((is_set_prod'.factors _ _).2 q₂).2 } }, 
    { fapply is_prod.set_prod.pair_unique,
      { change is_set_prod'.fst _ = _, rwr ((is_set_prod'.factors _ _).2 _).1,
        rwr <- is_prod.fst_hom.2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp },
      { change is_set_prod'.snd _ = _, rwr ((is_set_prod'.factors _ _).2 _).2,
        rwr <- is_prod.snd_hom.2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp } } }
end

@[hott]  --[GEVE]
def monoid_to_univ_product (M N P : Monoid) : 
  is_monoid_product M N P -> is_univ_monoid_product M N P :=
begin 
  intro is_prod, 
  let is_set_prod' := (equiv_char_of_products _ _ _).1 is_prod.set_prod,
  fapply is_univ_monoid_product.mk, 
  { exact is_prod.fst_hom.1 },
  { exact is_prod.snd_hom.1 },
  { intros Q q_M q_N, fapply dpair,
    { exact monoid_to_univ_prod_hom is_prod q_M q_N },
    { fapply prod.mk,
      { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp, 
        apply eq_of_homotopy, intro q,
        change Monoid_to_Set_functor.map is_prod.fst_hom.fst _ = _, 
        rwr ap10 is_prod.fst_hom.2, exact ((is_set_prod'.factors _ _).2 q).1 },
      { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp, 
        apply eq_of_homotopy, intro q,
        change Monoid_to_Set_functor.map is_prod.snd_hom.fst _ = _, 
        rwr ap10 is_prod.snd_hom.2, exact ((is_set_prod'.factors _ _).2 q).2 } } },
  { intros Q q_P q_P' M_eq N_eq, apply Monoid_to_Set_functor_is_faithful,  
    apply eq_of_homotopy, intro q, fapply is_prod.set_prod.pair_unique,
    { apply λ q, ap10 (is_prod.fst_hom.2)⁻¹ _ ⬝ q, apply λ q, q ⬝ ap10 is_prod.fst_hom.2 _,
      change (Monoid_to_Set_functor.map q_P ≫ Monoid_to_Set_functor.map is_prod.fst_hom.fst) q = 
             (Monoid_to_Set_functor.map q_P' ≫ Monoid_to_Set_functor.map is_prod.fst_hom.fst) q,
      rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, rwr M_eq },
    { apply λ q, ap10 (is_prod.snd_hom.2)⁻¹ _ ⬝ q, apply λ q, q ⬝ ap10 is_prod.snd_hom.2 _,
      change (Monoid_to_Set_functor.map q_P ≫ Monoid_to_Set_functor.map is_prod.snd_hom.fst) q = 
             (Monoid_to_Set_functor.map q_P' ≫ Monoid_to_Set_functor.map is_prod.snd_hom.fst) q,
      rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, rwr N_eq } }
end

@[hott]  --[GEVE]
def univ_to_monoid_product (M N P : Monoid) : 
  is_univ_monoid_product M N P -> is_monoid_product M N P :=
begin
  intro is_mon_prod, fapply is_monoid_product.mk,
  { fapply is_product.mk,
    { exact Monoid_to_Set_functor.map is_mon_prod.fst },
    { exact Monoid_to_Set_functor.map is_mon_prod.snd },
    { intros m n, fapply dpair,
      { fapply Monoid_to_Set_functor.map, exact List_Monoid One_Set, 
        { fapply (is_mon_prod.factors _ _).1,
          { apply (lists_are_free_monoid.map _).1, fapply One.rec, exact m }, 
          { apply (lists_are_free_monoid.map _).1, fapply One.rec, exact n } },
        { exact [One.star] } },
      { fapply prod.mk,
        { change (Monoid_to_Set_functor.map _ ≫ Monoid_to_Set_functor.map _) _ = _,
          rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, 
          rwr (is_mon_prod.factors _ _).2.1, 
          change Monoid_to_Set_functor.map (lists_are_free_monoid.map _).fst
                                                       (lists_are_free_monoid.h _) = m,
          rwr <- (lists_are_free_monoid.map _).2 },
        { change (Monoid_to_Set_functor.map _ ≫ Monoid_to_Set_functor.map _) _ = _,
          rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, 
          rwr (is_mon_prod.factors _ _).2.2, 
          change Monoid_to_Set_functor.map (lists_are_free_monoid.map _).fst
                                                       (lists_are_free_monoid.h _) = n,
          rwr <- (lists_are_free_monoid.map _).2 } } },
    { intros p p' fst_eq snd_eq, 
      let one_map_P : One_Set -> Monoid_to_Set_functor.obj P := by fapply One.rec; exact p,
      let free_hom_P : ↥(List_Monoid One_Set ⟶ P) := (lists_are_free_monoid.map one_map_P).1,
      let one_map_P' : One_Set -> Monoid_to_Set_functor.obj P := by fapply One.rec; exact p',
      let free_hom_P' : ↥(List_Monoid One_Set ⟶ P) := (lists_are_free_monoid.map one_map_P').1,
      have free_hom_eq : free_hom_P = free_hom_P', from 
      begin
        fapply is_mon_prod.unique,
        { apply lists_are_free_monoid.unique, intro o, hinduction o,
          rwr Monoid_to_Set_functor.map_comp, 
          change Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map free_hom_P 
                                                        (lists_are_free_monoid.h _)) = _,
          rwr <- (lists_are_free_monoid.map _).2, rwr fst_eq,
          rwr Monoid_to_Set_functor.map_comp,
          change _ = Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map free_hom_P' 
                                                       (lists_are_free_monoid.h _)),
          rwr <- (lists_are_free_monoid.map _).2 },
        { apply lists_are_free_monoid.unique, intro o, hinduction o,
          rwr Monoid_to_Set_functor.map_comp,
          change Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map free_hom_P
                                                          (lists_are_free_monoid.h _)) = _,
          rwr <- (lists_are_free_monoid.map _).2, rwr snd_eq,
          rwr Monoid_to_Set_functor.map_comp,
          change _ = Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map free_hom_P' 
                                                       (lists_are_free_monoid.h _)),
          rwr <- (lists_are_free_monoid.map _).2 }
      end,  
      have p_eq : Monoid_to_Set_functor.map free_hom_P [One.star] = p, from 
      begin 
        change (Monoid_to_Set_functor.map free_hom_P) (lists_are_free_monoid.h _) = _, 
        rwr <- (lists_are_free_monoid.map _).2 
      end,
      have p'_eq : (Monoid_to_Set_functor.map free_hom_P') [One.star] = p', from
      begin 
        change Monoid_to_Set_functor.map free_hom_P' (lists_are_free_monoid.h _) = _, 
        rwr <- (lists_are_free_monoid.map _).2 
      end,    
      rwr <- p_eq, rwr <- p'_eq, rwr free_hom_eq } },
  { fapply dpair is_mon_prod.fst, exact idp },
  { fapply dpair is_mon_prod.snd, exact idp }
end

@[hott]  --[GEVE]
def kernel_pair_submon {M N : Monoid} (f : M ⟶ N) : Submonoid (product_monoid M M) :=
begin
  let f' := Monoid_to_Set_functor.map f,
  fapply Submonoid_of_Subset,
  { intro m, exact to_Prop (f' m.1 = f' m.2) },
  { fapply submonoid_str.mk,
    { exact idp },
    { intros m₁ m₂ m₁_el m₂_el, 
      change Monoid_to_Set_functor.map f (m₁.1 * m₂.1) = Monoid_to_Set_functor.map f (m₁.2 * m₂.2), 
      rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
      change f' _ * f' _ = f' _ * f' _,
      have fst_eq : f' m₁.1 = f' m₁.2, from m₁_el,
      have snd_eq : f' m₂.1 = f' m₂.2, from m₂_el,
      rwr fst_eq, rwr snd_eq } }
end

/- We construct quotients of monoids as quotients of the underlying set by a congruence,
   with the induced monoid structure. Then we characterize monoid quotients by the 
   universal property. -/
@[hott]   --[GEVE]
class is_congruence {M : Type _} [has_mul M] (R : M -> M -> Prop)
  extends (is_equivalence (λ m n : M, R m n)) :=
(mul_comp : Π {m m' n n' : M}, R m m' -> R n n' -> R (m * n) (m' * n'))

@[hott]
def kernel_pair_to_rel {M N : Monoid} (f : M ⟶ N) : M -> M -> Prop :=
  λ m₁ m₂, to_Prop (Monoid_to_Set_functor.map f m₁ = Monoid_to_Set_functor.map f m₂)

@[hott]
def kernel_pair_to_cong {M N : Monoid} (f : M ⟶ N) : 
  is_congruence (kernel_pair_to_rel f) :=
begin
  fapply λ equiv_rel, @is_congruence.mk M _ (kernel_pair_to_rel f) equiv_rel,
  { fapply is_equivalence.mk,
    { intro m, exact idp },
    { intros m n p, exact p⁻¹ },
    { intros m n o p q, exact p ⬝ q } },
  { intros m m' n n' rel_m rel_n, 
    change Monoid_to_Set_functor.map f (m * n) = Monoid_to_Set_functor.map f (m' * n'),
    rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
    change _ = _ at rel_m, change _ = _ at rel_n, rwr rel_m, rwr rel_n } 
end

@[hott]  --[GEVE]
structure is_monoid_quotient {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1)
  [H : is_equivalence (λ m n, R m n)] (Q : Monoid.{u}) :=
(proj : M ⟶ Q)
(is_set_quot : @set.is_cons_quotient (set.to_Set M) R H (set.to_Set Q))
(proj_eq : Monoid_to_Set_functor.map proj = is_set_quot.proj)

@[hott]
structure Monoid_quotient {M : Monoid.{u}} (R : M -> M -> Prop)
  [H : is_equivalence (λ m n, R m n)] :=
(carrier : Monoid.{u})
(is_mon_quot : is_monoid_quotient R carrier)

@[hott]  --[GEVE]
def Monoid_cong_quotient {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1)
  [H : is_congruence R] : Monoid_quotient R :=
begin
  fapply Monoid_quotient.mk,
  { fapply Monoid.mk,
    { exact @set.set_quotient (Monoid_to_Set_functor.obj M) R },
    { fapply @monoid.mk,
      { apply_instance },
      { fapply set.set_quotient.rec2, 
        { intros m₁ m₂, exact set.set_class_of R (m₁ * m₂) },
        { intros m m' n rel, apply pathover_of_eq, apply set.eq_of_setrel, 
          fapply H.mul_comp, exact rel, exact is_equivalence.refl (λ m n, R m n) n },
        { intros m n n' rel, apply pathover_of_eq, apply set.eq_of_setrel, 
          fapply H.mul_comp, exact is_equivalence.refl (λ m n, R m n) m, exact rel } },
      { fapply set.set_quotient.prec3, intros m₁ m₂ m₃, apply set.eq_of_setrel, 
        have ass : m₁ * m₂ * m₃ = m₁ * (m₂ * m₃), from monoid.mul_assoc m₁ m₂ m₃, 
        rwr ass, exact is_equivalence.refl (λ m n, R m n) _ },
      { exact set.set_class_of R M.struct.one },
      { fapply set.set_quotient.prec, intro m, apply set.eq_of_setrel,
        have one_mul : monoid.one M.carrier * m = m, from monoid.one_mul m,
        rwr one_mul, exact is_equivalence.refl (λ m n, R m n) _ },
      { fapply set.set_quotient.prec, intro m, change M.carrier at m, apply set.eq_of_setrel,
        have mul_one : m * (monoid.one M.carrier) = m, from monoid.mul_one m,
        rwr mul_one, exact is_equivalence.refl (λ m n, R m n) _ } } },
  { fapply is_monoid_quotient.mk,
    { fapply monoid_hom.mk, exact @set.set_class_of (Monoid_to_Set_functor.obj M) R, 
      fapply monoid_hom_str.mk, 
      { intros m₁ m₂, exact idp },
      { exact idp } },
    { exact set.set_quotient_is_cons_quotient.{u u} R },
    { exact idp } }

end

@[hott]   --[GEVE]
def monoid_quotient_to_cong {M Q : Monoid} (R : M -> M -> Prop) 
  [H : is_equivalence (λ m n, R m n)] :
  is_monoid_quotient R Q -> (is_congruence R) :=
begin
  intro is_mon_quot, fapply is_congruence.mk, 
  intros m m' n n' rel_m rel_n, 
  apply (is_mon_quot.is_set_quot.eq _ _).1, rwr <- is_mon_quot.proj_eq, 
  rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
  rwr is_mon_quot.proj_eq, rwr (is_mon_quot.is_set_quot.eq _ _).2 rel_m, 
  rwr (is_mon_quot.is_set_quot.eq _ _).2 rel_n
end

@[hott]  --[GEVE]
structure is_univ_monoid_quotient {M : Monoid} (R : M -> M -> Prop)
  [H : is_equivalence (λ m n, R m n)] (Q : Monoid) :=
(proj : M ⟶ Q)
(rel_eq : Π (m₁ m₂ : M), R m₁ m₂ <-> 
                  Monoid_to_Set_functor.map proj m₁ = Monoid_to_Set_functor.map proj m₂)
(factors : Π {L : Monoid} (f : M ⟶ L), (Π (m₁ m₂ : M), R m₁ m₂ -> 
                     Monoid_to_Set_functor.map f m₁ = Monoid_to_Set_functor.map f m₂) -> 
                         Σ (g : Q ⟶ L), f = proj ≫ g)
(unique : Π {L : Monoid} (g₁ g₂ : Q ⟶ L), proj ≫ g₁ = proj ≫ g₂ -> g₁ = g₂)

@[hott] 
def univ_monoid_quotient_to_cong {M Q : Monoid} 
  (R : M -> M -> Prop) 
  [H : is_equivalence (λ m n, R m n)] :
  is_univ_monoid_quotient R Q -> (is_congruence R) :=
begin
  intro is_mon_quot, fapply is_congruence.mk, 
  intros m m' n n' rel_m rel_n, apply (is_mon_quot.rel_eq _ _).2, 
  rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
  rwr (is_mon_quot.rel_eq _ _).1 rel_m, rwr (is_mon_quot.rel_eq _ _).1 rel_n
end

@[hott]
def monoid_to_univ_quotient_map {M : Monoid.{u}} (R : M -> M -> Prop)
  [H : is_equivalence (λ m n, R m n)] (Q : Monoid) :
  is_monoid_quotient R Q -> Π {L : Monoid} (f : M ⟶ L) 
    (rel_eq : Π (m₁ m₂ : Monoid_to_Set_functor.obj M), R m₁ m₂ -> 
              Monoid_to_Set_functor.map f m₁ = Monoid_to_Set_functor.map f m₂), Q ⟶ L :=
begin
intros is_mon_quot L f rel_eq,
    { fapply monoid_hom.mk,
      { exact ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
               is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).1 },
      { fapply monoid_hom_str.mk,
        { intros q₁ q₂, hinduction is_mon_quot.is_set_quot.gen q₁ with p₁ fib₁, 
          hinduction is_mon_quot.is_set_quot.gen q₂ with p₂ fib₂,
          rwr <- fib₁.2, rwr <- fib₂.2, 
          rwr <- ap10 is_mon_quot.proj_eq, rwr <- ap10 is_mon_quot.proj_eq, 
          rwr <- (monoid_hom_laws _).mul_comp, 
          rwr ap10 is_mon_quot.proj_eq, rwr ap10 is_mon_quot.proj_eq, 
          rwr ap10 is_mon_quot.proj_eq,
          change (((set.cons_to_ind_quotient _ _ _).map _ _).1 ∘ 
                                          (set.cons_to_ind_quotient _ _ _).proj) _ = 
                 (((set.cons_to_ind_quotient _ _ _).map _ _).1 ∘ 
                                          (set.cons_to_ind_quotient _ _ _).proj) _ * 
                 (((set.cons_to_ind_quotient _ _ _).map _ _).1 ∘ 
                                          (set.cons_to_ind_quotient _ _ _).proj) _, 
          rwr <- ap10 ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
                   is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).2,
          rwr <- ap10 ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
                   is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).2,
          rwr <- ap10 ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
                  is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).2,
          rwr (monoid_hom_laws _).mul_comp },
    { rwr <- (monoid_hom_laws is_mon_quot.proj).one_comp, rwr ap10 is_mon_quot.proj_eq,
          change (((set.cons_to_ind_quotient _ _ _).map _ _).1 ∘ 
                                          (set.cons_to_ind_quotient _ _ _).proj) _ = _,
          rwr <- ap10 ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
                  is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).2,
          rwr (monoid_hom_laws _).one_comp } } }
end

@[hott]
def monoid_to_univ_quotient {M : Monoid.{u}} (R : M -> M -> Prop)
  [H : is_equivalence (λ m n, R m n)] (Q : Monoid.{u}) :
  is_monoid_quotient R Q -> is_univ_monoid_quotient R Q :=
begin
  intro is_mon_quot, fapply is_univ_monoid_quotient.mk,
  { exact is_mon_quot.proj },
  { intros m₁ m₂, fapply prod.mk, 
    { intro rel, rwr is_mon_quot.proj_eq, apply (is_mon_quot.is_set_quot.eq _ _).2, 
      exact rel },
    { intro p, apply (is_mon_quot.is_set_quot.eq _ _).1, rwr <- is_mon_quot.proj_eq,
      exact p } },
  { intros L f rel_eq, fapply dpair,
    { exact monoid_to_univ_quotient_map R Q is_mon_quot f rel_eq },
    { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp,
      change _ = _ ≫ _, rwr is_mon_quot.proj_eq,
      exact ((@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
               is_mon_quot.is_set_quot).map (Monoid_to_Set_functor.map f) rel_eq).2 } },
  { intros L g₁ g₂ fac_eq, apply Monoid_to_Set_functor_is_faithful,
    fapply (@set.cons_to_ind_quotient (Monoid_to_Set_functor.obj M) R _ _ 
                                                         is_mon_quot.is_set_quot).unique,
    change to_hom_set is_mon_quot.is_set_quot.proj ≫ Monoid_to_Set_functor.map _ =
           to_hom_set is_mon_quot.is_set_quot.proj ≫ Monoid_to_Set_functor.map _,
    rwr <- is_mon_quot.proj_eq,
    change Monoid_to_Set_functor.map _ ≫ _ = Monoid_to_Set_functor.map _ ≫ _,
    rwr <- Monoid_to_Set_functor.map_comp, rwr fac_eq }
end

@[hott]
def univ_iso_monoid_quotient {M : Monoid} (R : M -> M -> Prop)
  [H : is_congruence R] (Q : Monoid) (is_mon_quot : is_univ_monoid_quotient R Q) : 
  Σ (iso : (Monoid_cong_quotient R).carrier ≅ Q), is_mon_quot.proj =
      (Monoid_cong_quotient R).is_mon_quot.proj ≫ iso.hom :=
begin
  fapply dpair,
  { fapply iso.mk,
    { fapply λ rel_eq, ((monoid_to_univ_quotient _ _ 
               (Monoid_cong_quotient R).is_mon_quot).factors is_mon_quot.proj rel_eq).1, 
      intros m₁ m₂, exact (is_mon_quot.rel_eq _ _).1 },
    { fapply is_iso.mk,
      { fapply λ rel_eq, (is_mon_quot.factors (monoid_to_univ_quotient _ _ 
                                    (Monoid_cong_quotient R).is_mon_quot).proj rel_eq).1, 
        intros m₁ m₂, exact ((monoid_to_univ_quotient _ _ 
                                    (Monoid_cong_quotient R).is_mon_quot).rel_eq _ _).1 },
      { fapply is_mon_quot.unique _ (𝟙 Q), rwr is_precat.comp_id,
        rwr <- is_precat.assoc, 
        rwr <- (is_mon_quot.factors (monoid_to_univ_quotient _ _ 
                                    (Monoid_cong_quotient R).is_mon_quot).proj _).2,
        rwr <- ((monoid_to_univ_quotient _ _ 
               (Monoid_cong_quotient R).is_mon_quot).factors is_mon_quot.proj _).2 },
      { fapply (monoid_to_univ_quotient _ _ (Monoid_cong_quotient R).is_mon_quot).unique 
                                                                                 _ (𝟙 _), 
        rwr <- is_precat.assoc, 
        rwr <- ((monoid_to_univ_quotient _ _ 
               (Monoid_cong_quotient R).is_mon_quot).factors is_mon_quot.proj _).2,
        rwr <- (is_mon_quot.factors (monoid_to_univ_quotient _ _ 
                                    (Monoid_cong_quotient R).is_mon_quot).proj _).2 } } },
  { exact ((monoid_to_univ_quotient _ _ (Monoid_cong_quotient R).is_mon_quot).factors 
               is_mon_quot.proj _).2 }      
end

@[hott]  --[GEVE]
def univ_to_monoid_quotient {M : Monoid} (R : M -> M -> Prop)
  [H : is_equivalence (λ m n, R m n)] (Q : Monoid) :
  is_univ_monoid_quotient R Q -> is_monoid_quotient R Q :=
begin
  intro is_mon_quot, 
  let H' : is_congruence R, from univ_monoid_quotient_to_cong R is_mon_quot,
  let iso_Q := (@univ_iso_monoid_quotient _ R H' Q is_mon_quot).1,
  fapply is_monoid_quotient.mk,
  { exact is_mon_quot.proj },
  { fapply set.is_cons_quotient.mk,
    { exact Monoid_to_Set_functor.map is_mon_quot.proj },
    { intro q, hinduction (@Monoid_cong_quotient _ R H').is_mon_quot.is_set_quot.gen 
                            (Monoid_to_Set_functor.map iso_Q.ih.inv q) with tr_eq fib,
      apply tr, apply dpair fib.1, 
      have p : is_mon_quot.proj = (@Monoid_cong_quotient _ R H').is_mon_quot.proj ≫ 
                iso_Q.hom, from (@univ_iso_monoid_quotient _ R H' Q is_mon_quot).2,
      rwr p, rwr Monoid_to_Set_functor.map_comp, 
      rwr (@Monoid_cong_quotient _ R H').is_mon_quot.proj_eq, 
      change Monoid_to_Set_functor.map iso_Q.hom _ = _, 
      have p' : (@Monoid_cong_quotient _ R H').is_mon_quot.is_set_quot.proj fib.1 = 
                                    Monoid_to_Set_functor.map iso_Q.ih.inv q, from fib.2,
      rwr p', change (Monoid_to_Set_functor.map iso_Q.ih.inv ≫ 
                                        Monoid_to_Set_functor.map iso_Q.hom) q = q, 
      rwr <- Monoid_to_Set_functor.map_comp, rwr iso_Q.ih.r_inv },
    { intros m₁ m₂, fapply prod.mk, 
      exact (is_mon_quot.rel_eq _ _).2, exact (is_mon_quot.rel_eq _ _).1 } },
  { exact idp }
end

/- A congruence can be generated by arbitrary relations. -/
@[hott] 
inductive cong_sequence {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1) : 
  M -> M -> Type u
| rel {a b : M} (r : R a b) : cong_sequence a b
| refl (a : M) : cong_sequence a a
| symm {a b : M} (r : cong_sequence a b) : cong_sequence b a
| trans {a b c : M} (r : cong_sequence a b)  (r' : cong_sequence b c) : 
                                                                    cong_sequence a c
| mul {a a' b b' : M} (r : cong_sequence a a') (s : cong_sequence b b') : 
                                                        cong_sequence (a * b) (a' * b')

@[hott]  --[GEVE]
def rel_to_cong_rel {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1) : 
  M -> M -> Prop :=
  λ a b, ∥ cong_sequence R a b ∥

@[hott]
def cong_rel_ext_rel {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1) :
  Π m n : M, R m n -> rel_to_cong_rel R m n :=
λ m n rel, tr (cong_sequence.rel rel) 

@[hott, instance]
def cong_clos_rel_is_equiv_rel {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1) : 
  is_equivalence (λ a b, rel_to_cong_rel R a b) :=
begin
  fapply is_equivalence.mk,
  { intro a, exact tr (cong_sequence.refl R a) },
  { intros a b tr_seq, hinduction tr_seq with seq, exact tr (cong_sequence.symm seq) },
  { intros a b c tr_seq₁ tr_seq₂, 
    hinduction tr_seq₁ with seq₁, hinduction tr_seq₂ with seq₂,
    exact tr (cong_sequence.trans seq₁ seq₂) }
end

@[hott, instance]  --[GEVE]
def cong_clos_rel_is_cong_rel {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1) : 
  is_congruence (λ a b, rel_to_cong_rel R a b) :=
begin
  fapply is_congruence.mk,
  intros m m' n n' c_seq₁ c_seq₂, 
  hinduction c_seq₁ with seq₁, hinduction c_seq₂ with seq₂,
    exact tr (cong_sequence.mul seq₁ seq₂)
end 

@[hott]  --[GEVE]
def cong_clos_rel_is_min_cong {M : Monoid.{u}} (R : M -> M -> trunctype.{u} -1)
  (R' : M -> M -> trunctype.{u} -1) [H : is_congruence (λ a b, R' a b)] :
  (Π a b, R a b -> R' a b) -> (Π a b, rel_to_cong_rel R a b -> R' a b) :=
begin
  intros R'_ext_R a b rel_cong_R, hinduction rel_cong_R with seq, 
  hinduction seq,
  { exact R'_ext_R a b r },
  { exact is_equivalence.refl (λ a b, R' a b) a },
  { exact is_equivalence.symm (λ a b, R' a b) ih },
  { exact is_equivalence.trans (λ a b, R' a b) ih_r ih_r' },
  { exact is_congruence.mul_comp _ ih_r ih_s }
end

end algebra

end hott