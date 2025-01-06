import sets.product sets.quotients algebra.monoid.basic

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets subset hott.relation categories.sets

namespace algebra

/- We characterize free monoids by the recursion principle and by their freely generating
   constructors, and show that these characterisations imply each other. Then we construct
   a free monoid as a HIT and as the type of lists over the set of generators. -/
@[hott]
structure is_ind_free_monoid_of (A : Set.{u}) (F : Monoid.{u}) :=
  (h : A -> F)
  (map : Π {M : Monoid.{u}} (f : A -> M), Σ (g : F ⟶ M), 
                                     Π (a : A), f a = Monoid_to_Set_functor.map g (h a))
  (unique : Π {M : Monoid.{u}} (g₁ g₂ : F ⟶ M), (Π (a : A), 
      Monoid_to_Set_functor.map g₁ (h a) = Monoid_to_Set_functor.map g₂ (h a)) -> g₁ = g₂)

@[hott, reducible, instance]
def lists_are_monoid (A : Set.{u}) : monoid (list A) :=
begin
  fapply monoid.mk,
    { exact set.lists_are_set A },
    { exact list.append },
    { exact list_append_is_assoc },
    { exact [] },
    { intro l, exact idp },
    { exact list_append_nil }
end

@[hott, reducible]
def List_Monoid (A : Set.{u}) : Monoid :=
begin  
  fapply Monoid.mk,
  { exact list A },
  { exact lists_are_monoid A }
end

@[hott, instance]
def list_has_mul (A : Type u) [is_set A] : has_mul (list A) :=
begin 
  apply has_mul.mk, change List_Monoid (set.to_Set A) -> 
                           List_Monoid (set.to_Set A) -> List_Monoid (set.to_Set A),
  intros l₁ l₂, exact l₁ * l₂ 
end

@[hott]
def lists_are_free_monoid {A : Set.{u}} : is_ind_free_monoid_of A (List_Monoid A) :=
begin 
  fapply is_ind_free_monoid_of.mk,
  { intro a, exact [a] },
  { intros M f, fapply dpair,
    { fapply monoid_hom.mk,  
      { intro l, hinduction l, exact M.struct.one, exact f (hd) * ih },
      { fapply monoid_hom_str.mk,
        { intros l₁ l₂, hinduction l₁, 
          { hsimp, change _ = monoid.mul _ _, rwr monoid.one_mul },
          { hsimp, change _ = monoid.mul (monoid.mul _ _) _, rwr monoid.mul_assoc,
            change _ = _ * (_ * _), rwr <- ih } },
        { exact idp } } },
    { intro a, change f a = monoid.mul (f a) (monoid.one _), rwr monoid.mul_one } },
  { intros M g₁ g₂ p, fapply Monoid_to_Set_functor_is_faithful,
    apply eq_of_homotopy, intro l, hinduction l,
    { rwr (monoid_hom_laws g₁).one_comp, rwr (monoid_hom_laws g₂).one_comp },
    { change Monoid_to_Set_functor.map g₁ ([hd] * tl) = Monoid_to_Set_functor.map g₂ ([hd] * tl),
      rwr (monoid_hom_laws g₁).mul_comp, rwr (monoid_hom_laws g₂).mul_comp, rwr ih, rwr p } }
end 

/- We characterize and construct products of two monoids using products of the 
   underlying sets. This implies and is implied by the standard universl property. -/
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

/- A submonoid is a subobject in the category of monoids, but because of the faithful 
   forgetful functor to sets, the set map underlying the embedding monomorphism is also
   a monomorphism, that is, injective. So we can construct a submonoid as a subset of a 
   monoid inheriting the monoid structure. -/
@[hott]  --[GEVE]
def Submonoid (M : Monoid) := @subobject Monoid_Category M

@[hott, instance]
def submonoid_has_hom (M : Monoid) : has_hom (Submonoid M) :=
  by change has_hom (@subobject Monoid_Category M); apply_instance

@[hott]  --[GEVE]
def monoid_mon_is_inj {N M : Monoid} : Π (f : N ⟶ M), 
  @is_mono Monoid_Category _ _ f <-> 
  @set.is_set_injective (Monoid_to_Set_functor.obj M) (Monoid_to_Set_functor.obj N) 
                        (Monoid_to_Set_functor.map f) :=
begin                        
  intro f, apply prod.mk,
  { intro mono_f, intros n₁ n₂ p, 
    let g₁ : ↥(List_Monoid One_Set ⟶ N), from (lists_are_free_monoid.map (λ s, n₁)).1,
    let g₂ : ↥(List_Monoid One_Set ⟶ N), from (lists_are_free_monoid.map (λ s, n₂)).1,
    have p₁ : Monoid_to_Set_functor.map g₁ [One.star] = n₁, from 
                                    ((lists_are_free_monoid.map (λ s, n₁)).2 _)⁻¹,
    have p₂ : Monoid_to_Set_functor.map g₂ [One.star] = n₂, from 
                                    ((lists_are_free_monoid.map (λ s, n₂)).2 _)⁻¹,
    rwr <- p₁, rwr <- p₂, apply λ q, ap10 q [One.star], 
    apply ap (λ f, Monoid_to_Set_functor.map f),
    apply mono_f, apply lists_are_free_monoid.unique, intro s, hinduction s, 
    rwr Monoid_to_Set_functor.map_comp, rwr Monoid_to_Set_functor.map_comp,
    change Monoid_to_Set_functor.map f (Monoid_to_Set_functor.map g₁ [One.star]) = 
                    Monoid_to_Set_functor.map f (Monoid_to_Set_functor.map g₂ [One.star]),
    rwr p₁, rwr p₂, rwr p },
  { intro set_inj, 
    fapply λ H, @mono_is_faithful Monoid_Category Set_Category Monoid_to_Set_functor H 
                                  _ _ f, 
    apply Monoid_to_Set_functor_is_faithful, apply set_inj_is_mono _ set_inj }
end 

@[hott]  --[GEVE]
def Submonoid_of_Subset {M : Monoid} (N : Subset (Monoid_to_Set_functor.obj M)) : 
  @subset.elem (Monoid_to_Set_functor.obj M) M.struct.one N -> 
  (Π n₁ n₂ : N, @subset.elem (Monoid_to_Set_functor.obj M) 
                             (@monoid.mul M M.struct n₁.1 n₂.1) N) -> Submonoid M :=
begin  
  intros one_in prod_in, fapply subobject.mk,
  { apply Monoid.mk N, fapply monoid.mk,
    { apply_instance },
    { intros n₁ n₂, exact ⟨@monoid.mul M M.struct n₁.1 n₂.1, prod_in n₁ n₂⟩ },
    { intros n₁ n₂ n₃, apply pred_Set_eq, apply monoid.mul_assoc },
    { exact ⟨M.struct.one, one_in⟩ },
    { intros n, apply pred_Set_eq, apply monoid.one_mul },
    { intros n, apply pred_Set_eq, apply monoid.mul_one } },
  { fapply monoid_hom.mk, 
    { exact pred_Set_map _ },
    { fapply monoid_hom_str.mk,
      { intros n₁ n₂, exact idp },
      { exact idp } } },
  { apply (monoid_mon_is_inj _).2, exact pred_Set_map_is_inj _ }
end

@[hott]
def subset_of_submonoid {M : Monoid} (N : Submonoid M) : 
  Subset (Monoid_to_Set_functor.obj M) :=
λ m, image (Monoid_to_Set_functor.map N.hom) m 

@[hott]
def submonoid_hom_of_subset {M : Monoid.{u}} (N₁ N₂ : Submonoid.{u} M) :
  (subset_of_submonoid N₁ ⊆ subset_of_submonoid N₂) -> (N₁ ⟶ N₂) :=
begin
  intro sset, 
  have fib_n : Π n, fiber (Monoid_to_Set_functor.map N₂.hom) (Monoid_to_Set_functor.map N₁.hom n), from 
      λ n, set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N₂.is_mono)  
          (Monoid_to_Set_functor.map N₁.hom n) (sset _ (tr (fiber.mk n idp))), 
  fapply hom_of_monos.mk, 
  { fapply monoid_hom.mk,  
    { intro n₁, exact (fib_n n₁).1 },
    { fapply monoid_hom_str.mk,
      { intros n₁ n₁', apply (monoid_mon_is_inj.{u} _).1 N₂.is_mono, rwr (fib_n _).2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr (fib_n _).2, rwr (fib_n _).2 },
      { apply (monoid_mon_is_inj.{u} _).1 N₂.is_mono, rwr (fib_n _).2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp } } },
  { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp,
    apply eq_of_homotopy, intro n, 
    change Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map _ n) = 
                                                           Monoid_to_Set_functor.map _ n, 
    exact (fib_n _).2 }
end

/- Monoid homomorphisms have images. -/
@[hott, instance]  --[GEVE]
def monoid_hom_has_image {M N : Monoid.{u}} (f : M ⟶ N) : 
  @has_image Monoid_Category.{u} _ _ f :=
begin  
  fapply has_image.mk, apply tr, fapply cat_image.mk,
  { fapply Submonoid_of_Subset.{u},
    { exact (λ b : N.carrier, image (Monoid_to_Set_functor.map f) b) },
    { apply tr, apply fiber.mk M.struct.one, exact (monoid_hom_laws f).one_comp },
    { intros n₁ n₂, hinduction n₁ with n₁ im₁, hinduction n₂ with n₂ im₂,
      hinduction im₁ with fib₁, hinduction im₂ with fib₂, 
      apply tr, apply fiber.mk (fib₁.1 * fib₂.1), 
      rwr (monoid_hom_laws f).mul_comp, rwr fib₁.2, rwr fib₂.2 } },
  { fapply dpair,  
    { fapply monoid_hom.mk, 
      { intro m, fapply dpair, exact Monoid_to_Set_functor.map f m, 
        exact tr (fiber.mk m (@idp _ (Monoid_to_Set_functor.map f m))) },
      { fapply monoid_hom_str.mk,
        { intros m₁ m₂, apply pred_Set_eq, exact (monoid_hom_laws f).mul_comp _ _ },
        { apply pred_Set_eq, exact (monoid_hom_laws f).one_comp } } },
    { apply Monoid_to_Set_functor_is_faithful, exact idp } },
  { intros N' fac, fapply submonoid_hom_of_subset.{u},
    intros n el_im, change ↥(image _ _), change ↥(image _ _) at el_im,
    hinduction el_im with fib, change fiber (pred_Set_map _) n at fib,
    let p : fib.1.1 = n := fib.2,
    hinduction fib.1.2 with tr_eq m_fib, rwr <- p,
    apply tr, fapply fiber.mk, 
    { exact (Monoid_to_Set_functor.map fac.1) m_fib.1 }, 
    { change ((Monoid_to_Set_functor.map fac.fst) ≫ 
                             Monoid_to_Set_functor.map N'.hom) m_fib.1 = _, 
      rwr <- Monoid_to_Set_functor.map_comp, 
      have q : fac.1 ≫ N'.hom = f, from fac.2,
      rwr q, exact m_fib.2 } }
end

@[hott]  --[GEVE]
def gen_submonoid {M : Monoid} (L : Subset (Monoid_to_Set_functor.obj M)) :
  Submonoid M :=
@hom.image Monoid_Category _ _ (lists_are_free_monoid.map (pred_Set_map L)).1 
                               (monoid_hom_has_image _)

@[hott]
def gen_submonoid_min {M : Monoid} (L : Subset (Monoid_to_Set_functor.obj M)) :
  Π (N : Submonoid M), (L ⊆ (subset_of_submonoid N)) -> (gen_submonoid L ⟶ N) :=
begin
  intros N sset, fapply cat_image.univ, fapply dpair,
  { apply λ f, (lists_are_free_monoid.map f).1, intro m, 
    exact (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) m.1 
                                                                  (sset m.1 m.2)).1 },
  { fapply lists_are_free_monoid.unique, intro n, 
    rwr Monoid_to_Set_functor.map_comp, 
    change Monoid_to_Set_functor.map N.hom (Monoid_to_Set_functor.map 
              (lists_are_free_monoid.map _).fst (lists_are_free_monoid.h n)) = _,
    rwr <- (lists_are_free_monoid.map _).2 n, rwr <- (lists_are_free_monoid.map _).2 n,
    rwr (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) n.1 
                                                                  (sset n.1 n.2)).2 }
end 

@[hott]  --[GEVE]
def kernel_pair_submon {M N : Monoid} (f : M ⟶ N) : Submonoid (product_monoid M M) :=
begin
  let f' := Monoid_to_Set_functor.map f,
  fapply Submonoid_of_Subset,
  { intro m, exact to_Prop (f' m.1 = f' m.2) },
  { exact idp },
  { intros m₁ m₂, change Monoid_to_Set_functor.map f (m₁.1.1 * m₂.1.1) = 
                         Monoid_to_Set_functor.map f (m₁.1.2 * m₂.1.2), 
    rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
    change f' _ * f' _ = f' _ * f' _,
    have fst_eq : f' m₁.1.1 = f' m₁.1.2, from m₁.2,
    have snd_eq : f' m₂.1.1 = f' m₂.1.2, from m₂.2,
    rwr fst_eq, rwr snd_eq }
end

/- We construct quotients of monoids as quotients of the underlying set by a congruence,
   with the induced monoid structure. Then we characterize monoid quotients by the 
   universal property. -/
@[hott]   --[GEVE]
class is_congruence {M : Type _} [has_mul M] (R : M -> M -> Prop)
  extends (is_equivalence (λ m n : M, R m n)) :=
(mul_comp : Π (m m' n n' : M), R m m' -> R n n' -> R (m * n) (m' * n'))

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

end algebra

end hott