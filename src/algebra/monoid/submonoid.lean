import sets.product algebra.monoid.basic  

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets subset hott.relation categories.sets

namespace algebra

/- A submonoid is a subobject in the category of monoids, but because of the faithful 
   forgetful functor to sets, the set map underlying the embedding monomorphism is also
   a monomorphism, that is, injective. So we can construct a submonoid as a subset of a 
   monoid inheriting the monoid structure. -/
@[hott]  --[GEVE]
def Submonoid (M : Monoid) := subobject M

@[hott]
def subset_of_submonoid {M : Monoid} (N : Submonoid M) : 
  Subset (Monoid_to_Set_functor.obj M) :=
λ m, image (Monoid_to_Set_functor.map N.hom) m 

@[hott, instance]
def subset_of_monoid_mem {M : Monoid} : @has_mem M (Subset (Monoid_to_Set_functor.obj M)) :=
  has_mem.mk (λ (m : M) (N : Subset (Monoid_to_Set_functor.obj M)), 
                                            @subset.elem (Monoid_to_Set_functor.obj M) m N)                                                        

@[hott, instance]
def submonoid_mem {M : Monoid} : @has_mem M (Submonoid M) :=
  has_mem.mk (λ (m : M) (N : Submonoid M), @subset.elem (Monoid_to_Set_functor.obj M) m 
                                                        (subset_of_submonoid N))

@[hott, instance]
def submonoid_has_hom (M : Monoid) : has_hom (Submonoid M) :=
  by change has_hom (subobject M); apply_instance

@[hott, instance]
def submonoid_has_order (M : Monoid) : has_order (Submonoid M) :=
  by change has_order (subobject M); apply_instance

@[hott]  --[GEVE]
def monoid_mon_is_inj {N M : Monoid} : Π (f : N ⟶ M), 
  is_mono f <-> @set.is_set_injective (Monoid_to_Set_functor.obj M) (Monoid_to_Set_functor.obj N) 
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
    fapply λ H, @mono_is_faithful _ _ _ _ Monoid_to_Set_functor H _ _ f, 
    apply Monoid_to_Set_functor_is_faithful, apply set_inj_is_mono _ set_inj }
end 

@[hott]
structure submonoid_str {M : Monoid} (N : Subset (Monoid_to_Set_functor.obj M)) :=
  (one : monoid.one M ∈ N)
  (mul : Π {n₁ n₂ : M}, n₁ ∈ N -> n₂ ∈ N -> n₁ * n₂ ∈ N)

@[hott]  --[GEVE]
def Submonoid_of_Subset {M : Monoid} (N : Subset (Monoid_to_Set_functor.obj M)) : 
  submonoid_str N -> Submonoid M :=
begin  
  intro str, hinduction str with one_in prod_in, fapply subobject.mk,
  { apply Monoid.mk N, fapply monoid.mk,
    { apply_instance },
    { intros n₁ n₂, exact ⟨@monoid.mul M M.struct n₁.1 n₂.1, prod_in n₁.2 n₂.2⟩ },
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
def submonoid_laws {M : Monoid} (N : Submonoid M) : submonoid_str (subset_of_submonoid N) :=
begin
  fapply submonoid_str.mk,
  { apply tr, fapply fiber.mk, exact N.obj.struct.one, exact (monoid_hom_laws _).one_comp },
  { intros g₁ g₂ g₁_el g₂_el, hinduction g₁_el with fib₁, hinduction g₂_el with fib₂,
    apply tr, fapply fiber.mk, exact fib₁.1 * fib₂.1, rwr (monoid_hom_laws _).mul_comp,
    rwr fib₁.2, rwr fib₂.2 }
end 

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

@[hott]
def subset_of_submonoid_hom {M : Monoid.{u}} (N₁ N₂ : Submonoid.{u} M) :
  (N₁ ⟶ N₂) -> (subset_of_submonoid N₁ ⊆ subset_of_submonoid N₂) :=
begin
  intros sm_hom m m_el, hinduction m_el with fib,   
  rwr <- sm_hom.fac at fib, rwr Monoid_to_Set_functor.map_comp at fib, 
  apply tr, fapply fiber.mk,
  { exact Monoid_to_Set_functor.map sm_hom.hom_obj fib.1 },
  { exact fib.2 } 
end

/- Monoid homomorphisms have images. -/
@[hott, instance]  --[GEVE]
def monoid_hom_has_image {M N : Monoid.{u}} (f : M ⟶ N) : 
  has_image f :=
begin  
  fapply has_image.mk, 
  { fapply Submonoid_of_Subset.{u},
    { exact (λ b : N.carrier, image (Monoid_to_Set_functor.map f) b) },
    { fapply submonoid_str.mk, 
      { apply tr, apply fiber.mk M.struct.one, exact (monoid_hom_laws f).one_comp },
      { intros n₁ n₂ n₁_im n₂_im, hinduction n₁_im with fib₁, hinduction n₂_im with fib₂,
        apply tr, apply fiber.mk (fib₁.1 * fib₂.1), 
        rwr (monoid_hom_laws f).mul_comp, rwr fib₁.2, rwr fib₂.2 } } },
  { fapply is_image.mk, 
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
        rwr q, exact m_fib.2 } } }
end

@[hott]
def fiber_hom_im_hom {M M' : Monoid} (f : M ⟶ M') (m' : M') : 
  fiber (Monoid_to_Set_functor.map (hom.image f).hom) m' -> image (Monoid_to_Set_functor.map f) m' :=
begin
  intro fib, hinduction fib with g_im g_im_eq, hinduction g_im with imf, hinduction snd with fibf,
  apply tr, rwr <- g_im_eq, exact fibf
end

@[hott]
def fiber_hom_hom_im {M M' : Monoid} (f : M ⟶ M') (m' : M') : 
  fiber (Monoid_to_Set_functor.map f) m' -> fiber (Monoid_to_Set_functor.map (hom.image f).hom) m' :=
begin 
  intro fib_f, hinduction fib_f with m m_eq, fapply fiber.mk,
  { fapply dpair m', apply tr, exact fiber.mk m m_eq },
  { exact idp }
end

@[hott]
def mon_im_hom_to_set_im_map {M M' : Monoid} (f : M ⟶ M') :
  Monoid_to_Set_functor.map (hom.image f).hom = pred_Set_map (subset.Image (Monoid_to_Set_functor.map f)) :=
begin fapply eq_of_homotopy, intro im_m', exact idp end

@[hott]
def mon_hom_im_to_set_im {M M' : Monoid} (f : M ⟶ M') :
  subset_of_submonoid (hom.image f) = subset.Image (Monoid_to_Set_functor.map f) :=
begin
  fapply (subset.sset_eq_iff_inclusion _ _).2, fapply pair,
  { intros m' m'_el, hinduction m'_el with fib', rwr mon_im_hom_to_set_im_map f at fib', 
    hinduction fib' with im_n' im_n'_eq, hinduction im_n' with n' im_n', hinduction im_n' with fib,
    apply tr, fapply fiber.mk fib.1, rwr fib.2, exact im_n'_eq },
  { intros m' m'_el, 
    apply tr, fapply fiber.mk,
    { apply dpair m', exact m'_el },
    { exact idp } }
end 

@[hott]  --[GEVE]
def gen_submonoid {M : Monoid} {L : Set} (gen : L -> Monoid_to_Set_functor.obj M) :
  Submonoid M :=
hom.image (lists_are_free_monoid.map gen).1                                

@[hott]  --[GEVE]
def gen_submonoid_min {M : Monoid} {L : Set} (gen : L -> Monoid_to_Set_functor.obj M) :
  Π (N : Submonoid M), (Image gen ⊆ (subset_of_submonoid N)) -> (gen_submonoid gen ≼ N) :=
begin
  intros N sset, fapply is_image.univ (has_image.is_im _), fapply dpair,
  { apply λ f, (lists_are_free_monoid.map f).1, intro l, 
    exact (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) (gen l) (sset _ (tr ⟨l, idp⟩))).1 },
  { fapply lists_are_free_monoid.unique, intro l, 
    rwr Monoid_to_Set_functor.map_comp, 
    change Monoid_to_Set_functor.map N.hom (Monoid_to_Set_functor.map 
              (lists_are_free_monoid.map _).fst (lists_are_free_monoid.h l)) = _,
    rwr <- (lists_are_free_monoid.map _).2 l, rwr <- (lists_are_free_monoid.map _).2 l,
    rwr (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) (gen l) (sset _ (tr ⟨l, idp⟩))).2 }
end 

@[hott]
def gen_submonoid_subset {M : Monoid} {L : Set} (gen : L -> Monoid_to_Set_functor.obj M) :
  Π (m : M), image (Monoid_to_Set_functor.map (lists_are_free_monoid.map gen).1 ) m -> 
             m ∈ subset_of_submonoid (gen_submonoid gen) :=
begin 
  intros m m_im, hinduction m_im with fib,
  apply tr, apply fiber_hom_hom_im, exact fib 
end

@[hott]
def submonoid_im_comp {M M' M'' : Monoid} (f : M ⟶ M') (g : M' ⟶ M'') :
  hom.image (f ≫ g) = hom.image ((hom.image f).hom ≫ g) :=
begin
  fapply subobj_antisymm,
  { rwr <- hom_to_image_eq f, rwr is_precat.assoc, rwr hom_to_image_eq f, apply im_incl },
  { fapply submonoid_hom_of_subset, rwr mon_hom_im_to_set_im, rwr mon_hom_im_to_set_im, 
    rwr Monoid_to_Set_functor.map_comp, rwr Monoid_to_Set_functor.map_comp, 
    rwr mon_im_hom_to_set_im_map, intros m'' m''_el, hinduction m''_el with fib,
    hinduction fib with m' m'_eq, hinduction m' with m' im_m', hinduction im_m' with fib,
    apply tr, apply fiber.mk fib.1, rwr <- m'_eq,
    change Monoid_to_Set_functor.map g _ = Monoid_to_Set_functor.map g _, rwr fib.2 }
end 

@[hott]
def hom_gen_im_submonoid {M M' : Monoid} (f : M ⟶ M') {L : Set} (gen : L -> (Monoid_to_Set_functor.obj M)) :
  gen_submonoid (Monoid_to_Set_functor.map f ∘ gen) = hom.image ((gen_submonoid gen).hom ≫ f) :=
begin
  change hom.image _ = hom.image ((hom.image _).hom ≫ f), rwr free_monoid_comp_hom, 
  exact submonoid_im_comp _ _
end

end algebra

end hott