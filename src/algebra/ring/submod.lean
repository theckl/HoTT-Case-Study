import algebra.ring.examples 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets categories.colimits

namespace algebra

/- We define submodules as subobjects in the category of `R`-modules, that is, 
   ultimately by the universal property of mononmorphisms. Then we show that monomorphisms
   of modules have an underlying injective map of sets, and construct submodules from a few 
   structure axioms. -/
@[hott]  --[GEVE]
def Submodule {R : CommRing} (M : Module R) := @subobject (Module_Category R) M

@[hott, instance]
def submodule_has_hom {R : CommRing} (M : Module R) : has_hom (Submodule M) :=
  by change has_hom (@subobject (Module_Category R) M); apply_instance

@[hott, instance]
def submodule_has_order {R : CommRing} (M : Module R) : has_order (Submodule M) :=
  by change has_order (@subobject (Module_Category R) M); apply_instance

@[hott, instance]
def submodule_is_set {R : CommRing} (M : Module R) : is_set (Submodule M) :=
  by change is_set (@subobject (Module_Category R) M); apply_instance

@[hott] --[GEVE]
def mod_mono_is_inj {R : CommRing} {M N : Module R} : Π (f : M ⟶ N), 
  @is_mono (Module_Category R) _ _ f <-> 
  @set.is_set_injective ((Module_to_Set_functor R).obj N) ((Module_to_Set_functor R).obj M) 
                        ((Module_to_Set_functor R).map f) :=
begin
  intro f, apply prod.mk,
  { intro mono_f, intros m₁ m₂ f_eq, 
    have p : mod_to_mod_hom M m₁ = mod_to_mod_hom M m₂, from 
    begin 
      apply mono_f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy, intro r, 
      rwr (Module_to_Set_functor R).map_comp, rwr (Module_to_Set_functor R).map_comp,
      change ↥R at r, change (Module_to_Set_functor R).map f (r ⬝ m₁) = 
                                                (Module_to_Set_functor R).map f (r ⬝ m₂),
      rwr (module_hom_laws f).scal_mul_comp, rwr (module_hom_laws f).scal_mul_comp,
      rwr f_eq 
    end,
    rwr <- (module_laws M).one_scal_mul m₁, rwr <- (module_laws M).one_scal_mul m₂,
    change (Module_to_Set_functor R).map (mod_to_mod_hom M m₁) (1:R) = _, rwr p },
  { intro inj_f, intros L g₁ g₂ gf_eq, 
    apply Module_to_Set_functor_is_faithful, apply set_inj_is_mono _ inj_f, 
    rwr <- (Module_to_Set_functor R).map_comp, rwr <- (Module_to_Set_functor R).map_comp,
    rwr gf_eq }
end

@[hott]
def subset_of_submodule {R : CommRing} (M : Module R) (H : Submodule M) : 
  Subset ((Module_to_Set_functor R).obj M) :=
λ g, image ((Module_to_Set_functor R).map H.hom) g 

@[hott]
structure submodule_str {R : CommRing} {M : Module R}
  (N : Subset ((Module_to_Set_functor R).obj M)) :=
(add : Π (m₁ m₂ : (Module_to_Set_functor R).obj M), m₁ ∈ N -> m₂ ∈ N -> (m₁ + m₂) ∈ N)
(zero : (0 : (Module_to_Set_functor R).obj M) ∈ N)
(scal_mul : Π (r : R) (m : (Module_to_Set_functor R).obj M), m ∈ N -> (r ⬝ m) ∈ N)

@[hott]
def submodule_laws {R : CommRing} {M : Module R}
  (N : Submodule M) : submodule_str (subset_of_submodule M N) :=
begin
  fapply submodule_str.mk,
  { intros m₁ m₂ el₁ el₂, hinduction el₁ with fib₁, hinduction el₂ with fib₂,
    apply tr, apply fiber.mk (fib₁.1 + fib₂.1), rwr (module_hom_laws _).add_comp,
    rwr fib₁.2, rwr fib₂.2 },
  { apply tr, exact fiber.mk 0 (module_hom_laws _).zero_comp },
  { intros r m el_m, hinduction el_m with fib, apply tr, apply fiber.mk (r ⬝ fib.1), 
    rwr (module_hom_laws _).scal_mul_comp, rwr fib.2 }
end

@[hott]
def submodule_hom_of_subset {R : CommRing} {M : Module R} (N₁ N₂ : Submodule M) :
  (subset_of_submodule M N₁ ⊆ subset_of_submodule M N₂) -> (N₁ ⟶ N₂) :=
begin
  intro sset, 
  have fib_n : Π n, fiber ((Module_to_Set_functor R).map N₂.hom) 
                                     ((Module_to_Set_functor R).map N₁.hom n), from 
  begin intro n, fapply set.set_inj_image_to_fiber _ ((mod_mono_is_inj _).1 N₂.is_mono)  
          ((Module_to_Set_functor R).map N₁.hom n) (sset _ (tr (fiber.mk n idp))) end,
  fapply hom_of_monos.mk,
  { fapply module_hom.mk,
    { intro n₁, exact (fib_n n₁).1 },
    { fapply module_hom_str.mk,
      { intros n₁ n₁', apply (mod_mono_is_inj _).1 N₂.is_mono, rwr (fib_n _).2, 
        rwr (module_hom_laws _).add_comp, rwr (module_hom_laws _).add_comp,
        rwr (fib_n _).2, rwr (fib_n _).2 },
      { apply (mod_mono_is_inj _).1 N₂.is_mono, rwr (fib_n _).2,
        rwr (module_hom_laws _).zero_comp, rwr (module_hom_laws _).zero_comp },
      { intros r n₁, apply (mod_mono_is_inj _).1 N₂.is_mono, rwr (fib_n _).2,
        rwr (module_hom_laws _).scal_mul_comp, rwr (module_hom_laws _).scal_mul_comp,
        rwr (fib_n _).2 } } },
  { apply Module_to_Set_functor_is_faithful, rwr (Module_to_Set_functor R).map_comp,
    apply eq_of_homotopy, intro n, 
    change (Module_to_Set_functor R).map _ ((Module_to_Set_functor R).map _ n) = 
                                                      (Module_to_Set_functor R).map _ n, 
    exact (fib_n _).2 }
end


@[hott]
def subset_of_submod_hom {R : CommRing} {M : Module R} {N₁ N₂ : Submodule M} :
  (N₁ ⟶ N₂) -> (subset_of_submodule M N₁ ⊆ subset_of_submodule M N₂) :=
begin
  intros f g g_el₁, hinduction g_el₁ with fib₁, 
  rwr <- f.fac at fib₁, rwr (Module_to_Set_functor R).map_comp at fib₁, 
  apply tr, fapply fiber.mk,
  { exact (Module_to_Set_functor R).map f.hom_obj fib₁.1 },
  { exact fib₁.2 }
end

@[hott]
def Submodule_of_mod_Subset {R : CommRing} {M : Module R} 
  (N : Subset ((Module_to_Set_functor R).obj M)) :
  submodule_str N -> Module R :=
begin
  intro str, apply Module.mk N, fapply module.mk,
  { fapply ab_group.mk,
    { apply_instance },
    { intros n₁ n₂, exact ⟨n₁.1 + n₂.1, str.add _ _ n₁.2 n₂.2⟩ },
    { intros n₁ n₂ n₃, apply pred_Set_eq, apply (module_laws M).add_assoc },
    { exact ⟨0, str.zero⟩ },
    { intro n, apply pred_Set_eq, apply (module_laws M).zero_add },
    { intro n, apply pred_Set_eq, apply (module_laws M).add_zero },
    { intro n, fapply dpair (-n.1), rwr neg_eq_neg_one_scal_mul,
      exact str.scal_mul _ _ n.2 },
    { intro n, apply pred_Set_eq, apply (module_laws M).add_left_inv },
    { intros n₁ n₂, apply pred_Set_eq, apply (module_laws M).add_comm } },
  { intros r n, exact ⟨r ⬝ n.1, str.scal_mul _ _ n.2⟩ },
  { intro n, apply pred_Set_eq, apply (module_laws M).one_scal_mul },
  { intros r s n, apply pred_Set_eq, apply (module_laws M).scal_mul_assoc },
  { intros r s n, apply pred_Set_eq, apply (module_laws M).left_distr },
  { intros r s n, apply pred_Set_eq, apply (module_laws M).right_distr }
end

@[hott]  --[GEVE]
def Submodule_of_Subset {R : CommRing} {M : Module R} 
  (N : Subset ((Module_to_Set_functor R).obj M)) :
  submodule_str N -> Submodule M :=
begin
  intro str, fapply subobject.mk,
  { exact Submodule_of_mod_Subset N str },
  { fapply module_hom.mk,
    { exact pred_Set_map _ },
    { fapply module_hom_str.mk,
      { intros n₁ n₂, exact idp },
      { exact idp },
      { intros r n, exact idp } } },
  { apply (mod_mono_is_inj _).2, exact pred_Set_map_is_inj _ }
end

@[hott]  
def Submodule_Subset_str {R : CommRing} {M : Module R} 
  (N : Subset ((Module_to_Set_functor R).obj M))
  (N_str : submodule_str N) : subset_of_submodule M (Submodule_of_Subset N N_str) = N :=  
begin
  apply eq_of_homotopy, intro g, fapply iff_eq, fapply prod.mk,
  { intro ss_g, hinduction ss_g with fib, rwr <- fib.2, exact fib.1.2 },
  { intro H_g, apply tr, change fiber (pred_Set_map N) g, fapply fiber.mk,
    { fapply dpair, exact g, exact H_g },
    { exact idp } }
end

/- The zero-submodule is contained in every submodule (equivalently, is initial). -/
@[hott]
def zero_submodule {R : CommRing} (M : Module R) : Submodule M :=
begin  
  fapply subobject.mk, exact zero_Module R, exact initial_mod_hom M, 
  intros H f₁ f₂ f_eq, fapply Module_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro h, exact @is_prop.elim _ One_is_prop _ _
end

@[hott]  --[GEVE]
def zero_submodule_is_initial {R : CommRing} (M : Module R) : Π (N : Submodule M), 
  zero_submodule M ⟶ N :=
begin
  intro N, apply submodule_hom_of_subset, intros m m_el, 
  hinduction m_el with fib, hinduction fib with m' m'_eq, change One at m',
  have p : m' = One.star, from is_prop.elim _ _, 
  have m_one : m = 0, by rwr <- m'_eq,
  rwr m_one, apply tr, apply fiber.mk, exact (module_hom_laws N.hom).zero_comp
end

/- Ideals are submodules of `R^[1]`. -/
@[hott]  --[GEVE]
def Ideal (R : CommRing) := Submodule (R^[1])

/- Annihilator of a module element and of a submonoid of `R`. -/
@[hott]  --[GEVE]
def annihilator {R : CommRing} {M : Module R} (m : M) : Ideal R :=
begin
  fapply Submodule_of_Subset,
  { intro r, change ↥R at r, exact to_Prop (r ⬝ m = 0) },
  { fapply submodule_str.mk,
    { intros r₁ r₂ r₁_el r₂_el, change ↥R at r₁, change ↥R at r₂,
      change r₁ ⬝ m = 0 at r₁_el, change r₂ ⬝ m = 0 at r₂_el,
      change (r₁ + r₂) ⬝ m = 0, rwr (module_laws M).right_distr, rwr r₁_el, rwr r₂_el,
      rwr (module_laws M).add_zero },
    { change (0:R) ⬝ m = 0, rwr zero_scal_mul_zero },
    { intros r s s_el, change ↥R at s, change s ⬝ m = 0 at s_el, change (r * s) ⬝ m = 0,
      rwr (module_laws M).scal_mul_assoc, rwr s_el, rwr scal_mul_zero_zero } }
end

@[hott]
structure is_mul_closed {R : CommRing} (S : Subset (CommRing_to_Set_functor.obj R)) :=
  (one : (1 : CommRing_to_Set_functor.obj R) ∈ S)
  (clos : Π (s₁ s₂ : CommRing_to_Set_functor.obj R), s₁ ∈ S -> s₂ ∈ S -> s₁ * s₂ ∈ S)  

@[hott]  --[GEVE]
def annihilator_of_sset {R : CommRing} {S : Subset (CommRing_to_Set_functor.obj R)}
  (H : is_mul_closed S) : Ideal R :=
begin
  fapply Submodule_of_Subset,
  { intro r, change ↥R at r, 
    exact ∥ Σ (s : CommRing_to_Set_functor.obj R) (el : s ∈ S), r * s = 0 ∥ },
  { fapply submodule_str.mk,
    { intros r₁ r₂ r₁_el r₂_el, change ↥R at r₁, change ↥R at r₂,
      hinduction r₁_el with s₁_el, hinduction r₂_el with s₂_el, 
      apply tr, fapply dpair (s₁_el.1 * s₂_el.1), 
      fapply dpair (H.clos _ _ s₁_el.2.1 s₂_el.2.1), rwr comm_ring_laws.right_distrib,
      rwr <- comm_ring_laws.mul_assoc r₁, rwr <- comm_ring_laws.mul_assoc r₂,
      rwr comm_ring_laws.mul_comm r₂, rwr comm_ring_laws.mul_assoc _ r₂, 
      have p₁ : r₁ * s₁_el.fst = 0, from s₁_el.2.2, rwr p₁,
      have p₂ : r₂ * s₂_el.fst = 0, from s₂_el.2.2, rwr p₂,
      rwr ring.zero_mul, rwr ring.mul_zero, rwr add_zero },
    { apply tr, fapply dpair (1:R), fapply dpair H.one, exact ring.zero_mul (1:R) },
    { intros r s s_el, change ↥R at s, hinduction s_el with s_el,
      apply tr, fapply dpair s_el.1, fapply dpair s_el.2.1, change (r * s) * s_el.1 = 0,
      have p : s * s_el.1 = 0, from s_el.2.2, rwr comm_ring_laws.mul_assoc, rwr p, 
      exact ring.mul_zero _ } }
end

/- The kernel of a module homomorphism and a ring homomorphism. -/
@[hott]  --[GEVE]
def kernel_mod {R : CommRing} {M N : Module R} (f : M ⟶ N) : Submodule M :=
begin
  fapply Submodule_of_Subset,
  { intro m, exact to_Prop ((Module_to_Set_functor R).map f m = 0) },
  { fapply submodule_str.mk,
    { intros m₁ m₂ m₁_el m₂_el, 
      change (Module_to_Set_functor R).map f _ = _ at m₁_el,
      change (Module_to_Set_functor R).map f _ = _ at m₂_el,
      change (Module_to_Set_functor R).map f _ = _, rwr (module_hom_laws f).add_comp, 
      rwr m₁_el, rwr m₂_el, exact (module_laws N).add_zero 0 },
    { exact (module_hom_laws f).zero_comp },
    { intros r m m_el, change (Module_to_Set_functor R).map f _ = _ at m_el,
      change (Module_to_Set_functor R).map f _ = _, rwr (module_hom_laws f).scal_mul_comp,
      rwr m_el, exact scal_mul_zero_zero N r } }
end

@[hott]  --[GEVE]
def kernel_of_ring_hom {R S : CommRing} (f : R ⟶ S) : Ideal R :=
  kernel_mod (scalar_to_mod_hom f) 

@[hott]  --[GEVE]
def zero_kernel_is_mono {R : CommRing} {M N : Module R} (f : M ⟶ N) : 
  kernel_mod f = zero_submodule M <-> @is_mono (Module_Category R) _ _ f :=
begin
  fapply prod.mk,
  { intro ker_eq, apply (mod_mono_is_inj _).2, 
    intros m₁ m₂ m_eq, change ↥M at m₁, change ↥M at m₂, apply module_left_cancel M (-m₁),
    rwr (module_laws M).add_left_inv, 
    have el : ↥(subset_of_submodule M (zero_submodule M) (-m₁ + m₂)), from 
    begin
      rwr <- ker_eq, apply tr, fapply fiber.mk,
      { fapply dpair (-m₁+m₂), change (Module_to_Set_functor R).map f _ = _,
        rwr (module_hom_laws f).add_comp, rwr <- m_eq, rwr <- (module_hom_laws f).add_comp, 
        rwr (module_laws M).add_left_inv, exact (module_hom_laws f).zero_comp },
      { exact idp }
    end,
    hinduction el with el, apply eq.inverse, exact el.2⁻¹ },
  { intro mono_f, fapply subobj_antisymm,
    { apply submodule_hom_of_subset, intros m m_el, hinduction m_el with m_el, 
      hinduction m_el with n n_eq, hinduction n with n p, 
      change (Module_to_Set_functor R).map f n = 0 at p, change n = m at n_eq,
      apply tr, fapply fiber.mk One.star, rwr <- n_eq, change 0 = n,
      apply (mod_mono_is_inj f).1 mono_f, rwr p, exact (module_hom_laws f).zero_comp },
    { apply zero_submodule_is_initial M (kernel_mod f) } }
end

/- Module homomorphisms have images. -/
@[hott, instance]  
def module_hom_has_image {R : CommRing} {M N : Module R} (f : M ⟶ N) : 
  @has_image (Module_Category R) _ _ f :=
begin  
  fapply has_image.mk, fapply cat_image.mk,
  { fapply Submodule_of_Subset,
    { exact (λ n : N.carrier, image ((Module_to_Set_functor R).map f) n) },
    { fapply submodule_str.mk,
      { intros n₁ n₂ n₁_el n₂_el, hinduction n₁_el with fib₁, hinduction n₂_el with fib₂,
        apply tr, apply fiber.mk (fib₁.1 + fib₂.1), 
        rwr (module_hom_laws f).add_comp, rwr fib₁.2, rwr fib₂.2 },
      { apply tr, apply fiber.mk (0:M), exact (module_hom_laws f).zero_comp },
      { intros r n n_el, hinduction n_el with fib, apply tr, 
        fapply fiber.mk (r ⬝ fib.1), rwr (module_hom_laws f).scal_mul_comp, rwr fib.2 } } },
  { fapply dpair,  
    { fapply module_hom.mk, 
      { intro m, fapply dpair, exact (Module_to_Set_functor R).map f m, 
        exact tr (fiber.mk m (@idp _ ((Module_to_Set_functor R).map f m))) },
      { fapply module_hom_str.mk,
        { intros m₁ m₂, apply pred_Set_eq, exact (module_hom_laws f).add_comp _ _ },
        { apply pred_Set_eq, exact (module_hom_laws f).zero_comp },
        { intros r m, apply pred_Set_eq, exact (module_hom_laws f).scal_mul_comp _ _ } } },
    { apply Module_to_Set_functor_is_faithful, exact idp } },
  { intros N' fac, fapply submodule_hom_of_subset, 
    intros n el_im, change ↥(image _ _), change ↥(image _ _) at el_im,
    hinduction el_im with fib, change fiber (pred_Set_map _) n at fib,
    let p : fib.1.1 = n := fib.2,
    hinduction fib.1.2 with tr_eq n_fib, rwr <- p, apply tr, fapply fiber.mk, 
    { exact ((Module_to_Set_functor R).map fac.1) n_fib.1 },
    { change (((Module_to_Set_functor R).map fac.fst) ≫ 
                             (Module_to_Set_functor R).map N'.hom) n_fib.1 = _, 
      rwr <- (Module_to_Set_functor R).map_comp, 
      have q : fac.1 ≫ N'.hom = f, from fac.2,
      rwr q, exact n_fib.2 } }
end

set_option pp.universes true

/- Elements of a module generate a submodule; the sum of submodules is a submodule. -/
@[hott]
def gen_Submodule  {R : CommRing} {M : Module R} (gen : Subset (set.to_Set M.carrier)) :
  Submodule M :=
hom.image (@copi.desc _ _ _ (λ m : pred_Set gen, R^[1]) 
    (module_has_sum (λ m : pred_Set gen, R^[1])) _ (λ m : pred_Set gen, mod_to_mod_hom M m.1))

@[hott]
def sum_mod_submodule {R : CommRing} {M : Module R} {I : Set} (N : I -> Submodule M) :
  Submodule M :=
hom.image (@copi.desc _ _ _ (λ i : I, (N i).obj) (module_has_sum _) _ (λ i : I, (N i).hom)) 

end algebra

end hott