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
@[hott]
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
@[hott]
structure is_unit {R : CommRing} (u : R) :=
  (inv : R)
  (has_inv : inv * u = 1)

@[hott]
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

@[hott, instance]
def CommRing_concrete_sigma_system : 
  concrete_sigma_system CommRing.to_AddAbGroup.{u} AddAbGroup_CommRing_str :=
begin
  fapply concrete_sigma_system.mk, 
  { intro R, apply λ eqv, (fiber.fiber_pr1 AddAbGroup_CommRing_str R)⁻¹ᵉ ⬝e eqv,
    apply λ eqv, eqv ⬝e (fiber.equiv_precompose CommRing.to_AddAbGroup 
                                                AddAbGroup_CommRing_str_eqv_CommRing R),
    apply fiber_homotopy_equiv, exact CommRing_AddAbGroup_proj_homotopy },
  { intros R str₁ str₂, fapply equiv.mk,
    { intro p, change str₁ = str₂ at p, rwr p, exact 𝟙 _ },
    { fapply adjointify,
      { hinduction str₁ with ops₁ laws₁, hinduction str₂ with ops₂ laws₂,
        hinduction ops₁ with mul₁ one₁, hinduction ops₂ with mul₂ one₂,
        intro h, fapply sigma.sigma_eq,
        { hinduction R with R abg_R, hinduction abg_R with is_set_R,
          hinduction h with h_ss h_eq, hinduction h_ss with h h_laws,
          hinduction h_laws with h_one h_mul,
          --change h = (idtoiso idp).hom ≫ (idtoiso idp).hom at h_eq,
          --change h = 𝟙 (AddAbGroup.mk R (addabgroup.mk is_set_R _ _ _ _ _ _)) at h_eq,
          change h.1.1.1.1.1.1 one₁ = one₂ at h_one, 
          --change one₁ = one₂, rwr <- h_one,
          --rwr h_eq
          sorry },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
      { intro h, exact is_prop.elim _ _ },
      { intro h, exact is_set.elim _ _ } } }
end

@[hott, instance]
def CommRing_is_cat : is_cat.{u u+1} CommRing.{u} := by apply_instance

@[hott]
def CommRing_Category : Category :=
  Category.mk CommRing.{u} CommRing_is_cat

/-
@[hott, instance]
def CommRing_sigma_fibs_are_cat : 
  sigma_fibs_are_cat (λ (R : AddAbGroup_Category.{u}), 
                   Σ (ops : mul_monoid_ops_str R), mul_monoid_laws_str R ops) :=
begin
  fapply sigma_fibs_are_cat.mk,
  { intros G mon₁ mon₂ g g_eq,
    have p : ((concrete_full_hom_equiv (concrete_obj_system.fib_eqv 
                CommRing.to_AddAbGroup (λ (R : ↥AddAbGroup_Category), 
          Σ (ops : mul_monoid_ops_str R), mul_monoid_laws_str R ops))).map 
                                       g.1).1.1.1.1.1.1 = g.1.1.1.1.1.1.1, from 
    begin 
      hinduction G with G G_struct, hinduction G_struct, 
      apply λ p', ap sigma.fst (ap sigma.fst (ap sigma.fst (ap sigma.fst 
                            (ap sigma.fst (ap sigma.fst p'))))), 
      --hinduction laws₁, hinduction laws₂, 
      change _ ≫ g.1 ≫ _ = _, 
      --rwr is_precat.comp_id, rwr is_precat.id_comp 
      sorry
    end, 
    have g_eq_carrier : g.1.1.1.1.1.1.1 = (𝟙 (Magma.to_Set _)), from 
          ap sigma.fst (ap sigma.fst (ap sigma.fst (ap sigma.fst (ap sigma.fst 
                                                       (ap sigma.fst g_eq))))),
    hinduction mon₁ with ops₁ laws₁, hinduction mon₂ with ops₂ laws₂,
    fapply sigma.sigma_eq,
    { hinduction ops₁ with mul₁ one₁, hinduction ops₂ with mul₂ one₂,
      fapply ap011 mul_monoid_ops_str.mk,
      { apply eq_of_homotopy2, intros r₁ r₂,
        have q : g.1.1.1.1.1.1.1 (mul₁ r₁ r₂) = mul₁ r₁ r₂, from 
          ap10 g_eq_carrier (mul₁ r₁ r₂),
        rwr <- q, rwr <- p, --rwr g.2.2, 
        have q₁ : g.1.1.1.1.1.1.1 r₁ = r₁, from ap10 g_eq_carrier r₁,
        have q₂ : g.1.1.1.1.1.1.1 r₂ = r₂, from ap10 g_eq_carrier r₂,
        rwr <- q₁, rwr <- q₂, sorry },
      { have q : g.1.1.1.1.1.1.1 one₁ = one₁, from ap10 g_eq_carrier one₁,                                               
        rwr <- q, rwr <- p, exact g.2.1 } },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros G mon, apply λ H, @is_set.elim _ H, 
    exact set.dprod_of_Sets_is_set' _ _ }
end
-/
end algebra

end hott