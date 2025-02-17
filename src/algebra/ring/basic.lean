import algebra.group.basic 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

/- Commutative rings with one -/
@[hott] structure CommRing :=
  (carrier : Type _) 
  (struct : comm_ring carrier)

instance has_coe_CommRing : has_coe_to_sort CommRing.{u} :=
  ⟨Type u, CommRing.carrier⟩

attribute [instance] CommRing.struct

/- For later calculations, the ring laws should be available with `0`, `1`, `*`, 
   `+`, `-` and `⁻¹` - the `rwr`-tactic does not accept these notations from the 
   commutative ring structure directly. -/
@[hott] --[GEVE]
structure comm_ring_str {R : CommRing} :=
  (add_assoc : Π (r₁ r₂ r₃ : R), (r₁ + r₂) + r₃ = r₁ + (r₂ + r₃))
  (add_zero : Π r : R, r + 0 = r)
  (zero_add : Π r : R, 0 + r = r)
  (add_left_inv : Π r : R, (-r) + r = 0)
  (add_comm : Π (r s : R), r + s = s + r)
  (mul_assoc : Π (r₁ r₂ r₃ : R), (r₁ * r₂) * r₃ = r₁ * (r₂ * r₃))
  (mul_one : Π r : R, r * 1 = r)
  (one_mul : Π r : R, 1 * r = r)
  (left_distrib : Π (r s t : R), r * (s + t) = r * s + r * t)
  (right_distrib : Π (r s t : R), (r + s) * t = r * t + s * t)
  (mul_comm : Π (r s : R), r * s = s * r)
  
@[hott]
def comm_ring_laws {R : CommRing} : @comm_ring_str R :=
  comm_ring_str.mk comm_ring.add_assoc comm_ring.add_zero comm_ring.zero_add 
                   comm_ring.add_left_inv comm_ring.add_comm comm_ring.mul_assoc 
                   comm_ring.mul_one comm_ring.one_mul comm_ring.left_distrib 
                   comm_ring.right_distrib comm_ring.mul_comm

/- Units and their unique inverses in rings. -/
@[hott]  --[GEVE]
structure is_unit {R : CommRing} (u : R) :=
  (inv : R)
  (has_inv : inv * u = 1)

@[hott]  --[GEVE]
def inverse_is_unique {R : CommRing} (u : R) :
  Π (inv₁ inv₂ : R), inv₁ * u = 1 -> inv₂ * u = 1 -> inv₁ = inv₂ :=
begin
  intros inv₁ inv₂ law₁ law₂,
  calc inv₁ = inv₁ * 1 : (comm_ring_laws.mul_one _)⁻¹
       ... = inv₁ * (inv₂ * u) : by rwr law₂
       ... = inv₁ * (u * inv₂) : by rwr comm_ring_laws.mul_comm inv₂
       ... = (inv₁ * u) * inv₂ : (comm_ring_laws.mul_assoc _ _ _)⁻¹ 
       ... = 1 * inv₂ : by rwr law₁
       ... = inv₂ : comm_ring_laws.one_mul _
end

/- Commutative rings with one are a concrete category over abelian groups, with fibers
   having the structure of commutative monoids. -/
@[hott, reducible, hsimp]
def CommRing.to_AddAbGroup : CommRing.{u} -> AddAbGroup_Category.{u} :=
  λ R, AddAbGroup.mk R (@add_ab_group_of_ring R (comm_ring.to_ring R))

@[hott]
structure mul_monoid_ops_str (R : AddAbGroup_Category) :=
  (mul : R.carrier -> R.carrier -> R.carrier)
  (one : R.carrier)

@[hott, instance]
def mul_monoid_ops_is_set (R : AddAbGroup_Category) : is_set (mul_monoid_ops_str R) :=
begin
  have eqv : mul_monoid_ops_str R ≃ 
                         (R.carrier -> R.carrier -> R.carrier) × R.carrier, from 
  begin
    fapply equiv.mk, 
    { intro str, exact ⟨str.mul, str.one⟩ },
    { fapply adjointify, 
      { intro mul_one, exact mul_monoid_ops_str.mk mul_one.1 mul_one.2 },
      { intro mul_one, hinduction mul_one, exact idp },
      { intro str, hinduction str, exact idp } }
  end,  
  apply is_trunc_equiv_closed_rev 0 eqv, apply_instance
end

@[hott]
structure mul_monoid_laws_str (R : AddAbGroup_Category) (ops : mul_monoid_ops_str R) :=  
  (mul_assoc : Π r₁ r₂ r₃ : R.carrier, ops.mul (ops.mul r₁ r₂) r₃ = ops.mul r₁ (ops.mul r₂ r₃))
  (mul_one : Π r : R.carrier, ops.mul r ops.one = r)
  (one_mul : Π r : R.carrier, ops.mul ops.one r = r)
  (mul_comm : Π (r s : R.carrier), ops.mul r s = ops.mul s r)
  (left_distrib : Π (r s t : R.carrier), ops.mul r (s + t) = (ops.mul r s) + (ops.mul r t))
  (right_distrib : Π (r s t : R.carrier), ops.mul (r + s) t = (ops.mul r t) + (ops.mul s t))

@[hott, instance]
def mul_monoid_laws_is_prop {R : AddAbGroup_Category} (ops : mul_monoid_ops_str R) :
  is_prop (mul_monoid_laws_str R ops) :=
begin 
  apply is_prop.mk, intros laws₁ laws₂, hinduction laws₁, hinduction laws₂,
  fapply ap_6 mul_monoid_laws_str.mk, exact is_prop.elim _ _, exact is_prop.elim _ _,
  exact is_prop.elim _ _, exact is_prop.elim _ _, exact is_prop.elim _ _, 
  exact is_prop.elim _ _
end

@[hott, reducible, instance]
def CommRing_hom_system : concrete_hom_system CommRing.to_AddAbGroup.{u} :=
begin
  fapply concrete_hom_system.mk,
  { intros R S h, fapply @trunctype.mk -1,
    { exact (h.1.1.1.1.1.1 R.struct.one = S.struct.one) ×  
            (Π (r₁ r₂ : R), h.1.1.1.1.1.1 (@comm_ring.mul R.carrier _ r₁ r₂) = 
              @comm_ring.mul S.carrier _ (h.1.1.1.1.1.1 r₁) (h.1.1.1.1.1.1 r₂)) },
    { apply_instance } },
  { intro R, exact ⟨idp, (λ r₁ r₂, idp)⟩ },
  { intros R S T g h el_g el_h, fapply prod.mk,
    { change h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _) = _, rwr el_g.1, exact el_h.1 },
    { intros r₁ r₂, change h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _) = 
                @comm_ring.mul T.carrier _ (h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _)) 
                                           (h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _)), 
      rwr el_g.2, exact el_h.2 _ _ } },
  { intros R S g g_iso g_el, fapply prod.mk,
    { change g_iso.inv.1.1.1.1.1.1 S.struct.one = R.struct.one, 
      have p : g.1.1.1.1.1.1 R.struct.one = S.struct.one, from g_el.1,
      rwr <- p, change (g ≫ g_iso.inv).1.1.1.1.1.1 R.struct.one = R.struct.one, 
      rwr g_iso.l_inv },
    { intros s₁ s₂, 
      change g_iso.inv.1.1.1.1.1.1 (@comm_ring.mul S.carrier _ 
        ((𝟙 (CommRing.to_AddAbGroup S) : CommRing.to_AddAbGroup S ⟶ 
                CommRing.to_AddAbGroup S).1.1.1.1.1.1 s₁) 
              ((𝟙 (CommRing.to_AddAbGroup S) : CommRing.to_AddAbGroup S ⟶ 
                                  CommRing.to_AddAbGroup S).1.1.1.1.1.1 s₂)) = _,
    rwr <- g_iso.r_inv, 
    change g_iso.inv.1.1.1.1.1.1 (@comm_ring.mul S.carrier _ (g.1.1.1.1.1.1 _) 
                                                            (g.1.1.1.1.1.1 _)) = _, 
    rwr <- g_el.2, change (g ≫ g_iso.inv).1.1.1.1.1.1 _ = _, 
    rwr g_iso.l_inv } }
end

@[hott]
def AddAbGroup_CommRing_str : AddAbGroup_Category.{u} -> Type u :=
  λ R, Σ (ops : mul_monoid_ops_str R), mul_monoid_laws_str R ops  

@[hott, instance]
def AddAbGroup_CommRing_str_is_set : 
  Π R : AddAbGroup_Category.{u}, is_set (AddAbGroup_CommRing_str R) :=
begin 
  intro R, change is_set (Σ (ops : mul_monoid_ops_str R), mul_monoid_laws_str R ops), 
  apply_instance 
end

@[hott, instance]
def CommRing_fib_hom_system : fib_hom_system AddAbGroup_CommRing_str :=
begin
  fapply fib_hom_system.mk,
  { intro R, apply_instance },
  { intros R str₁ str₂, fapply Set.mk (str₁ = str₂), apply_instance },
  { intros R str₁ str₂, apply_instance }
end

@[hott, instance]
def CommRing_fibs_are_cat : sigma_fibs_are_cat AddAbGroup_CommRing_str :=
  begin fapply sigma_fibs_are_cat.mk, intros R str₁ str₂ h, exact h end

@[hott, reducible]
def AddAbGroup_CommRing_str_eqv_CommRing : 
  (Σ (R : AddAbGroup.{u}) (ops : mul_monoid_ops_str R), mul_monoid_laws_str R ops) ≃
  CommRing.{u} :=
begin
  fapply equiv.mk,
  { intro R_struct, apply CommRing.mk R_struct.1.carrier,
    exact comm_ring.mk R_struct.1.struct'.is_set_carrier R_struct.1.struct'.mul 
        R_struct.1.struct'.mul_assoc R_struct.1.struct'.one R_struct.1.struct'.one_mul 
        R_struct.1.struct'.mul_one R_struct.1.struct'.inv 
        R_struct.1.struct'.mul_left_inv R_struct.1.struct'.mul_comm
        R_struct.2.1.mul R_struct.2.2.mul_assoc R_struct.2.1.one R_struct.2.2.one_mul
        R_struct.2.2.mul_one R_struct.2.2.left_distrib 
        R_struct.2.2.right_distrib R_struct.2.2.mul_comm },
  { fapply adjointify,
    { intro R, fapply dpair, exact CommRing.to_AddAbGroup R, fapply dpair,
      { exact mul_monoid_ops_str.mk (CommRing.struct R).mul (CommRing.struct R).one },
      { exact mul_monoid_laws_str.mk (CommRing.struct R).mul_assoc 
           (CommRing.struct R).mul_one (CommRing.struct R).one_mul 
           (CommRing.struct R).mul_comm (CommRing.struct R).left_distrib 
           (CommRing.struct R).right_distrib } },
    { intro R, hinduction R with R R_struct, hinduction R_struct, exact idp },
    { intro R_struct, hinduction R_struct with R mon_struct, hinduction R with R, 
      hinduction struct', hinduction mon_struct with ops laws, hinduction ops, hinduction laws, 
      exact idp } }
end

@[hott]
def CommRing_AddAbGroup_proj_homotopy : Π (R_str : Σ (R : AddAbGroup_Category.{u}), 
  AddAbGroup_CommRing_str R), sigma.fst R_str = 
                  CommRing.to_AddAbGroup (AddAbGroup_CommRing_str_eqv_CommRing R_str) :=
begin
  intro R_str, hinduction R_str with R str, hinduction R with R abg_R,
  hinduction abg_R, exact idp
end

@[hott, reducible]
def AddAbGroup_CommRing_str_eqv_fiber : Π (R : AddAbGroup_Category.{u}),
  AddAbGroup_CommRing_str R ≃ fiber CommRing.to_AddAbGroup R :=
λ R, (fiber.fiber_pr1 AddAbGroup_CommRing_str R)⁻¹ᵉ ⬝e 
     (fiber_homotopy_equiv CommRing_AddAbGroup_proj_homotopy R) ⬝e 
     (fiber.equiv_precompose CommRing.to_AddAbGroup AddAbGroup_CommRing_str_eqv_CommRing R)  

@[hott]
def AddAbGroup_CommRing_str_to_fiber_eq {R : AddAbGroup_Category.{u}} : 
  Π (str : AddAbGroup_CommRing_str R), 
    ((AddAbGroup_CommRing_str_eqv_fiber R).to_fun str).2 =
            ((fiber_homotopy_equiv CommRing_AddAbGroup_proj_homotopy R).to_fun 
                                                            (fiber.mk ⟨R,str⟩ idp)).2 :=
λ str, idp

@[hott]
def AddAbGroup_CommRing_str_to_fiber_idp {R : Type u} {is_set_R : is_set R}
  {mul : R -> R -> R} {mul_assoc : Π r s t, mul (mul r s) t = mul r (mul s t)}
  {one : R} {one_mul : Π r, mul one r = r} {mul_one : Π r, mul r one = r}
  {inv : R -> R} {mul_left_inv : Π r, mul (inv r) r = one} 
  {mul_comm : Π r s, mul r s = mul s r} : 
  let R' := AddAbGroup.mk R (ab_group.mk is_set_R mul mul_assoc one one_mul mul_one
                                         inv mul_left_inv mul_comm) in
  Π (str : AddAbGroup_CommRing_str R'), ((fiber_homotopy_equiv 
        CommRing_AddAbGroup_proj_homotopy R').to_fun (fiber.mk ⟨R',str⟩ idp)).2 = idp :=
λ str, idp

@[hott, instance]
def CommRing_concrete_sigma_system : 
  concrete_sigma_system CommRing.to_AddAbGroup.{u} AddAbGroup_CommRing_str :=
begin
  fapply concrete_sigma_system.mk, 
  { intro R, exact AddAbGroup_CommRing_str_eqv_fiber R },
  { intro R, intros str₁ str₂, fapply equiv.mk,
    { intro p, change str₁ = str₂ at p, rwr p, exact 𝟙 _ },
    { fapply adjointify,
      { intro h, hinduction h with h_ss h_eq, hinduction h_ss with h h_laws,
        rwr AddAbGroup_CommRing_str_to_fiber_eq str₁ at h_eq,
        rwr AddAbGroup_CommRing_str_to_fiber_eq str₂ at h_eq,
        hinduction R with R abg_R, hinduction abg_R,
        rwr AddAbGroup_CommRing_str_to_fiber_idp at h_eq,
        rwr AddAbGroup_CommRing_str_to_fiber_idp at h_eq,
        change h = _ at h_eq,
        have h_eq' : h.1.1.1.1.1.1 = 𝟙 (Set.mk R is_set_carrier), by rwr h_eq,
        fapply sigma.sigma_eq,
        { hinduction str₁ with ops₁ laws₁, hinduction str₂ with ops₂ laws₂,
          hinduction ops₁ with mul₁ one₁, hinduction ops₂ with mul₂ one₂,
          hinduction h_laws with h_one h_mul,
          change h.1.1.1.1.1.1 one₁ = one₂ at h_one,
          change Π r₁ r₂, h.1.1.1.1.1.1 (mul₁ r₁ r₂) = 
                                            mul₂ (h.1.1.1.1.1.1 r₁) (h.1.1.1.1.1.1 r₂) at h_mul,
          fapply ap011 (mul_monoid_ops_str.mk),
          { apply eq_of_homotopy2, intros r₁ r₂, 
            change _ = mul₂ ((𝟙 (Set.mk R is_set_carrier) : R -> R) r₁) 
                            ((𝟙 (Set.mk R is_set_carrier) : R -> R) r₂),
            rwr <- h_eq', rwr <- h_mul, rwr h_eq' },
          { rwr <- h_one, rwr h_eq' } },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
      { intro h, exact is_prop.elim _ _ },
      { intro h, exact is_set.elim _ _ } } }
end

@[hott, instance]
def CommRing_is_cat : is_cat.{u u+1} CommRing.{u} := by apply_instance

@[hott]
def CommRing_Category : Category :=
  Category.mk CommRing.{u} CommRing_is_cat

/- For calculations with ring homomorphisms, it is more effective to extract the laws
   of a homomorphism. -/
@[hott, reducible]
def CommRing_to_Set_functor : CommRing ⥤ Set :=
begin
  apply λ F, concrete_forget_functor (CommRing.to_AddAbGroup) ⋙ F,
  apply λ F, concrete_forget_functor (AddAbGroup.to_AbGroup) ⋙ F,
  apply λ F, concrete_forget_functor (AbGroup.to_Group) ⋙ F,
  exact Group_to_Set_functor
end   

@[hott]
def CommRing_to_Set_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Π (l : CommRing_to_Set_functor.obj R), 
       (CommRing_to_Set_functor.map f ≫ CommRing_to_Set_functor.map g) l =
        CommRing_to_Set_functor.map g (CommRing_to_Set_functor.map f l) := 
λ l, idp 

@[hott, instance]
def CommRing_Set_has_add (R : CommRing) : has_add (CommRing_to_Set_functor.obj R) :=
  begin apply has_add.mk, change R -> R -> R, intros r₁ r₂, exact r₁ + r₂ end

@[hott, instance]
def CommRing_Set_has_zero (R : CommRing) : has_zero (CommRing_to_Set_functor.obj R) :=
  begin apply has_zero.mk, change ↥R, exact 0 end

@[hott, instance]
def CommRing_Set_has_neg (R : CommRing) : has_neg (CommRing_to_Set_functor.obj R) :=
  begin apply has_neg.mk, change R -> R, intro r, exact -r end  

@[hott, instance]
def CommRing_Set_has_mul (R : CommRing) : has_mul (CommRing_to_Set_functor.obj R) :=
  begin apply has_mul.mk, change R -> R -> R, intros r₁ r₂, exact r₁ * r₂ end

@[hott, instance]
def CommRing_Set_has_one (R : CommRing) : has_one (CommRing_to_Set_functor.obj R) :=
  begin apply has_one.mk, change ↥R, exact 1 end  

@[hott]  --[GEVE]
structure comm_ring_hom_str {R S : CommRing} (f : R.carrier -> S.carrier) :=
  (add_comp : Π (r₁ r₂ : R), f (r₁ + r₂) = f r₁ + f r₂)
  (zero_comp : f 0 = 0)
  (mul_comp : Π (r₁ r₂ : R), f (r₁ * r₂) = f r₁ * f r₂)
  (one_comp : f 1 = 1) 

@[hott]
def comm_ring_hom_laws {R S : CommRing} (f : R ⟶ S) : 
  comm_ring_hom_str (CommRing_to_Set_functor.map f) :=
comm_ring_hom_str.mk f.1.1.1.1.1.1.2 f.1.1.1.1.2 f.2.2 f.2.1  

@[hott]  --[GEVE]
def comm_ring_hom.mk {R S : CommRing} (f : R -> S) : 
  comm_ring_hom_str f -> (R ⟶ S) :=
λ str, ⟨⟨⟨⟨⟨⟨⟨f, str.add_comp⟩, true.intro⟩, str.zero_comp⟩, true.intro⟩, true.intro⟩, 
                             true.intro⟩, ⟨str.one_comp, str.mul_comp⟩⟩ 

@[hott] 
def CommRing_to_Set_functor_is_faithful : is_faithful_functor (CommRing_to_Set_functor) :=
begin 
  fapply faithful_is_trans (concrete_forget_functor (CommRing.to_AddAbGroup)), 
  { apply @concrete_forget_functor_is_faithful _ _ CommRing.to_AddAbGroup },
  { fapply faithful_is_trans (concrete_forget_functor (AddAbGroup.to_AbGroup)), 
    { apply @concrete_forget_functor_is_faithful _ _ AddAbGroup.to_AbGroup },
    { fapply faithful_is_trans (concrete_forget_functor (AbGroup.to_Group)),
      { apply @concrete_forget_functor_is_faithful _ _ AbGroup.to_Group },
      { apply Group_to_Set_functor_is_faithful } } } 
end 

end algebra

end hott