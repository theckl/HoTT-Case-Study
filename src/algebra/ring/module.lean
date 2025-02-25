import algebra.ring.basic nat2 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets hott.nat

class has_act (α : Type _) (β : Type _) := (scal_mul : α → β → β)
infix ⬝ := has_act.scal_mul

namespace algebra

@[hott] 
structure module (R : CommRing.{u}) (M : Type u) extends ab_group M :=
  (scal_mul : R -> M -> M)
  (one_scal_mul : Π m : M, scal_mul 1 m = m)
  (scal_mul_assoc : Π (r s : R) (m : M), scal_mul (r * s) m = scal_mul r (scal_mul s m))
  (left_distr : Π (r : R) (m n : M), scal_mul r (mul m n) = 
                                                      mul (scal_mul r m) (scal_mul r n))
  (right_distr : Π (r s : R) (m : M), scal_mul (r + s) m = 
                                                      mul (scal_mul r m) (scal_mul s m))

attribute [class] module

@[hott, reducible, instance] 
def add_ab_group_of_module (R : CommRing.{u}) (M : Type u) [H : module R M] : 
  add_ab_group M :=
@module.to_ab_group R M H

@[hott, instance]
def has_act_module (R : CommRing.{u}) (M : Type u) [H : module R M] :
  has_act R M := has_act.mk H.scal_mul

@[hott] 
structure Module (R : CommRing.{u}) :=
  (carrier : Type u) 
  (struct : module R carrier)

instance has_coe_Module (R : CommRing.{u}) : has_coe_to_sort (Module.{u} R) :=
  ⟨Type u, Module.carrier⟩

attribute [instance] Module.struct

/- Sums of finitely many elements of a module -/
@[hott]
def module_sum_of_tuple {R : CommRing} {M : Module R} {n : ℕ} :
  tuple M n -> M :=
begin
  hinduction n,
  { intro t, exact 0 },
  { intro t, exact ih (@tuple.split_left _ n 1 t) + t ⟨n, nat.le_refl (n+1)⟩ }
end

/- For later calculations, the module laws should be available with `0`, `1`, `*`, 
   `+`, `-` and `⁻¹` - the `rwr`-tactic does not accept these notations from the 
   module structure directly. -/
@[hott] --[GEVE]
structure module_str {R : CommRing} {M : Module R} :=
  (add_assoc : Π (m₁ m₂ m₃ : M), (m₁ + m₂) + m₃ = m₁ + (m₂ + m₃))
  (add_zero : Π m : M, m + 0 = m)
  (zero_add : Π m : M, 0 + m = m)
  (add_left_inv : Π m : M, (-m) + m = 0)
  (add_comm : Π (m n : M), m + n = n + m)
  (one_scal_mul : Π m : M, (1 : R) ⬝ m = m)
  (scal_mul_assoc : Π (r s : R) (m : M), (r * s) ⬝ m  = r ⬝ (s ⬝ m))
  (left_distr : Π (r : R) (m n : M), r ⬝ (m + n) = r ⬝ m + r ⬝ n)
  (right_distr : Π (r s : R) (m : M), (r + s) ⬝ m = r ⬝ m + s ⬝ m)

@[hott]
def module_laws {R : CommRing} (M : Module R) : @module_str R M :=
  module_str.mk M.struct.to_ab_group.mul_assoc M.struct.to_ab_group.mul_one
                M.struct.to_ab_group.one_mul M.struct.to_ab_group.mul_left_inv
                M.struct.to_ab_group.mul_comm M.struct.one_scal_mul
                M.struct.scal_mul_assoc M.struct.left_distr M.struct.right_distr  

@[hott]
def module_left_cancel {R : CommRing} (M : Module R) : Π (m m₁ m₂ : M),
  m + m₁ = m + m₂ -> m₁ = m₂ :=
begin 
  intros m m₁ m₂ p, rwr <- (module_laws M).zero_add m₁,  
  rwr <- (module_laws M).zero_add m₂, rwr <- (module_laws M).add_left_inv m,
  rwr (module_laws M).add_assoc, rwr (module_laws M).add_assoc, rwr p, 
end 

@[hott]
def scal_mul_zero_zero {R : CommRing} (M : Module R) : 
  Π (r : R), r ⬝ (0 : M) = 0 :=
begin
  intro r, fapply module_left_cancel M (r ⬝ 0) (r ⬝ 0) 0,
  rwr <- (module_laws M).left_distr, rwr (module_laws M).add_zero,
  rwr (module_laws M).add_zero
end 

@[hott]
def module_sum_of_tuples_add {R : CommRing} {M : Module R} {n : ℕ} :
  Π (s t : tuple M n), module_sum_of_tuple (λ i : fin n, s i + t i) =
                                      module_sum_of_tuple s + module_sum_of_tuple t :=
begin
  hinduction n,
  { intros s t, change (0 : M) = 0 + 0, exact ((module_laws M).add_zero (0 : M))⁻¹ },
  { intros s t, 
    change (module_sum_of_tuple _) + (s _ + t _) = ((module_sum_of_tuple _) + (s _)) +
                                                    ((module_sum_of_tuple _) + (t _)),
    rwr (module_laws M).add_assoc, rwr <- (module_laws M).add_assoc (s _),
    rwr (module_laws M).add_comm (s _) (module_sum_of_tuple _), 
    rwr (module_laws M).add_assoc _ (s _), 
    rwr <- (module_laws M).add_assoc _ (module_sum_of_tuple _), rwr <- ih }
end

@[hott]
def module_sum_of_tuples_zero {R : CommRing} {M : Module R} (n : ℕ) :
  module_sum_of_tuple (λ i : fin n, (0 : M)) = 0 :=
begin
  hinduction n, exact idp, change module_sum_of_tuple (λ (i : fin n), 0) + 0 = 0,
  rwr ih, rwr (module_laws M).add_zero
end

@[hott]
def module_sum_of_tuples_scal_mul {R : CommRing} {M : Module R} {n : ℕ} :
  Π (r : R) (s : tuple M n), module_sum_of_tuple (λ i : fin n, r ⬝ (s i)) =
                                      r ⬝ module_sum_of_tuple s :=
begin
  hinduction n,
  { intros r s, exact (scal_mul_zero_zero M r)⁻¹ },
  { intros r s, change module_sum_of_tuple (λ i : fin n, r ⬝ _) + r ⬝ _ = 
                                                       r ⬝ (module_sum_of_tuple _ + _),
    rwr ih r (λ i : fin n, s (@fin_lift n 1 i)), rwr (module_laws M).left_distr }
end

@[hott]
def module_sum_of_tuple_comp {R : CommRing} {M : Module R} {n : ℕ} :
  Π (m : M) (i : fin n),
    module_sum_of_tuple (λ (j : fin n), dite (i = j) (λ p, m) (λ np, (0 : M))) = m :=
begin
  hinduction n, 
  { intros m i, hinduction nat.not_lt_zero i.val i.is_lt },
  { intros m i, change module_sum_of_tuple (λ (j : fin n), dite _ _ _) + dite _ _ _ = _,
    hinduction fin.has_decidable_eq i ⟨n, nat.le_refl (n+1)⟩ with dec p np,
    { change _ + m = _, apply λ r, eq.concat r ((module_laws M).zero_add m),
      apply ap (λ k, k + m), apply λ r, eq.concat r (module_sum_of_tuples_zero n), 
      apply ap module_sum_of_tuple, apply eq_of_homotopy, intro j, 
      change dite _ _ _ = (0 : M), 
      have np : ¬(i = @fin_lift n 1 j), from 
        begin rwr p, intro q, exact nat.lt_irrefl n (nat.lt_of_le_of_lt 
                                            (nat.le_of_eq (ap fin.val q)) j.is_lt) end,
      exact dif_neg np },
    { change _ + 0 = m, rwr (module_laws M).add_zero, 
      have q : i.val < n, from 
        begin fapply nat.lt_of_le_prod_ne, exact nat.le_of_lt_succ i.is_lt, intro ne,
                                                               exact np (fin_eq ne) end,
      apply λ r, eq.concat r (ih m (@fin_desc n 1 i q)), apply ap module_sum_of_tuple, 
      apply eq_of_homotopy, intro j, change @dite _ _ M _ _ = @dite _ _ M _ _, 
      fapply equiv_dite,
      { fapply prod.mk, 
        { intro p, rwr <- @fin_desc_lift n 1 j j.is_lt, fapply apd011 (@fin_desc n 1) p,
          apply pathover_of_tr_eq, exact is_prop.elim _ _ }, 
        { intro p, rwr <- @fin_lift_desc n 1 i q, exact ap fin_lift p } },
      { intros p₁ q₁, exact idp },
      { intros np₁ nq₁, exact idp } } }
end 


/- Modules over a fixed commutative ring with one are a concrete category over 
   (additive) abelian groups. -/
@[hott, reducible, hsimp]
def Module.to_AddAbGroup {R : CommRing.{u}} : Module.{u} R -> AddAbGroup_Category.{u} :=
  λ M, AddAbGroup.mk M (add_ab_group_of_module R M)

@[hott]
structure scal_ops_str (R : CommRing.{u}) (M : AddAbGroup_Category.{u}) :=
  (mul : R -> M.carrier -> M.carrier)

@[hott, instance]
def scal_ops_is_set (R : CommRing) (M : AddAbGroup_Category) : 
  is_set (scal_ops_str R M) :=
begin
  have eqv : scal_ops_str R M ≃ (R -> M.carrier -> M.carrier), from 
  begin
    fapply equiv.mk, 
    { intro str, exact str.mul },
    { fapply adjointify, 
      { intro mul, exact scal_ops_str.mk mul },
      { intro mul, exact idp },
      { intro str, hinduction str, exact idp } }
  end,  
  apply is_trunc_equiv_closed_rev 0 eqv, apply_instance
end

@[hott]
structure scal_laws_str {R : CommRing} {M : AddAbGroup_Category} 
  (ops : scal_ops_str R M) := 
(one_mul : Π m : M.carrier, ops.mul 1 m = m) 
(mul_assoc : Π (r s : R) (m : M.carrier), ops.mul (r * s) m = ops.mul r (ops.mul s m))
(left_distrib : Π (r : R) (m n : M.carrier), ops.mul r (m + n) = 
                                                         (ops.mul r m) + (ops.mul r n))
(right_distrib : Π (r s : R) (m : M.carrier), ops.mul (r + s) m = 
                                                         (ops.mul r m) + (ops.mul s m))

@[hott, instance]
def scal_laws_is_prop {R : CommRing} {M : AddAbGroup_Category} (ops : scal_ops_str R M) :
  is_prop (scal_laws_str ops) :=
begin 
  apply is_prop.mk, intros mul₁ mul₂, hinduction mul₁, hinduction mul₂,
  fapply ap_4 scal_laws_str.mk, exact is_prop.elim _ _, exact is_prop.elim _ _,
  exact is_prop.elim _ _, exact is_prop.elim _ _
end

@[hott, reducible, instance]
def Module_hom_system (R : CommRing.{u}) : 
  concrete_hom_system (@Module.to_AddAbGroup.{u} R) :=
begin
  fapply concrete_hom_system.mk,
  { intros M N h, fapply @trunctype.mk -1,
    { exact (Π (r : R) (m : M), h.1.1.1.1.1.1 (module.scal_mul M.struct r m) = 
              module.scal_mul N.struct r (h.1.1.1.1.1.1 m)) },
    { apply_instance } },
  { intro M, exact λ r m, idp },
  { intros L M N g h el_g el_h,
    intros r m, change h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _) = 
                module.scal_mul N.struct r (h.1.1.1.1.1.1 (g.1.1.1.1.1.1 _)), 
      rwr el_g, exact el_h _ _ },
  { intros M N g g_iso g_el, 
    { intros r n, 
      change g_iso.inv.1.1.1.1.1.1 (module.scal_mul N.struct r 
              ((𝟙 (Module.to_AddAbGroup N) : Module.to_AddAbGroup N ⟶ 
                                  Module.to_AddAbGroup N).1.1.1.1.1.1 n)) = _,
    rwr <- g_iso.r_inv, 
    change g_iso.inv.1.1.1.1.1.1 (module.scal_mul N.struct r (g.1.1.1.1.1.1 _)) = _, 
    rwr <- g_el, change (g ≫ g_iso.inv).1.1.1.1.1.1 _ = _, rwr g_iso.l_inv } }
end

@[hott]
def AddAbGroup_Module_str (R : CommRing.{u}) : AddAbGroup_Category.{u} -> Type u :=
  λ M, Σ (ops : scal_ops_str R M), scal_laws_str ops  

@[hott, instance]
def AddAbGroup_Module_str_is_set (R : CommRing.{u}) : 
  Π M : AddAbGroup_Category.{u}, is_set (AddAbGroup_Module_str R M) :=
begin 
  intro M, change is_set (Σ (ops : scal_ops_str R M), scal_laws_str ops), 
  apply_instance 
end

@[hott, instance]
def Module_fib_hom_system (R : CommRing.{u}) : 
  fib_hom_system (AddAbGroup_Module_str R) :=
begin
  fapply fib_hom_system.mk,
  { intro M, apply_instance },
  { intros M str₁ str₂, fapply Set.mk (str₁ = str₂), apply_instance },
  { intros M str₁ str₂, apply_instance }
end

@[hott, instance]
def Module_fibs_are_cat (R : CommRing.{u}) : 
  sigma_fibs_are_cat (AddAbGroup_Module_str R) :=
begin fapply sigma_fibs_are_cat.mk, intros M str₁ str₂ h, exact h end

@[hott, reducible]
def AddAbGroup_Module_str_eqv_Module (R : CommRing.{u}) : 
  (Σ (M : AddAbGroup.{u}) (ops : scal_ops_str R M), scal_laws_str ops) ≃ Module.{u} R :=
begin
  fapply equiv.mk,
  { intro M_struct, apply Module.mk M_struct.1.carrier,
    exact module.mk M_struct.1.struct' M_struct.2.1.mul M_struct.2.2.one_mul
        M_struct.2.2.mul_assoc M_struct.2.2.left_distrib M_struct.2.2.right_distrib },
  { fapply adjointify,
    { intro M, fapply dpair, exact Module.to_AddAbGroup M, fapply dpair,
      { exact scal_ops_str.mk M.struct.scal_mul },
      { exact scal_laws_str.mk M.struct.one_scal_mul M.struct.scal_mul_assoc 
                               M.struct.left_distr M.struct.right_distr } },
    { intro M, hinduction M with M M_struct, hinduction M_struct, exact idp },
    { intro M_struct, hinduction M_struct with M mod_struct, hinduction M with M, 
      hinduction struct', hinduction mod_struct with ops laws, hinduction ops, 
      hinduction laws, exact idp } }
end

@[hott]
def Module_AddAbGroup_proj_homotopy (R : CommRing.{u}) : 
  Π (M_str : Σ (M : AddAbGroup_Category.{u}), AddAbGroup_Module_str R M), 
    sigma.fst M_str = Module.to_AddAbGroup (AddAbGroup_Module_str_eqv_Module R M_str) :=
begin
  intro M_str, hinduction M_str with M str, hinduction M with M abg_M,
  hinduction abg_M, exact idp
end

@[hott, reducible]
def AddAbGroup_Module_str_eqv_fiber (R : CommRing.{u}) : Π (M : AddAbGroup_Category.{u}),
  AddAbGroup_Module_str R M ≃ fiber (@Module.to_AddAbGroup R) M :=
λ M, (fiber.fiber_pr1 (AddAbGroup_Module_str R) M)⁻¹ᵉ ⬝e 
     (fiber_homotopy_equiv (Module_AddAbGroup_proj_homotopy R) M) ⬝e 
     (fiber.equiv_precompose (@Module.to_AddAbGroup R) 
                             (AddAbGroup_Module_str_eqv_Module R) M)  

@[hott]
def AddAbGroup_Module_str_to_fiber_eq {R : CommRing.{u}} {M : AddAbGroup_Category.{u}} : 
  Π (str : AddAbGroup_Module_str R M), 
    ((AddAbGroup_Module_str_eqv_fiber R M).to_fun str).2 =
            ((fiber_homotopy_equiv (Module_AddAbGroup_proj_homotopy R) M).to_fun 
                                                            (fiber.mk ⟨M,str⟩ idp)).2 :=
λ str, idp

@[hott]
def AddAbGroup_Module_str_to_fiber_idp {R : CommRing.{u}} {M : Type u} 
  {is_set_M : is_set M} {mul : M -> M -> M} 
  {mul_assoc : Π l m n, mul (mul l m) n = mul l (mul m n)}
  {one : M} {one_mul : Π m, mul one m = m} {mul_one : Π m, mul m one = m}
  {inv : M -> M} {mul_left_inv : Π m, mul (inv m) m = one} 
  {mul_comm : Π m n, mul m n = mul n m} : 
  let M' := AddAbGroup.mk M (ab_group.mk is_set_M mul mul_assoc one one_mul mul_one
                                         inv mul_left_inv mul_comm) in
  Π (str : AddAbGroup_Module_str R M'), ((fiber_homotopy_equiv 
        (Module_AddAbGroup_proj_homotopy R) M').to_fun (fiber.mk ⟨M',str⟩ idp)).2 = idp :=
λ str, idp

@[hott, instance]
def Module_concrete_sigma_system {R : CommRing.{u}} : 
  concrete_sigma_system (@Module.to_AddAbGroup.{u} R) (AddAbGroup_Module_str R) :=
begin
  fapply concrete_sigma_system.mk, 
  { intro M, exact AddAbGroup_Module_str_eqv_fiber R M },
  { intro M, intros str₁ str₂, fapply equiv.mk,
    { intro p, change str₁ = str₂ at p, rwr p, exact 𝟙 _ },
    { fapply adjointify,
      { intro h, hinduction h with h_ss h_eq, hinduction h_ss with h h_laws,
        rwr AddAbGroup_Module_str_to_fiber_eq str₁ at h_eq,
        rwr AddAbGroup_Module_str_to_fiber_eq str₂ at h_eq,
        hinduction M with M abg_M, hinduction abg_M,
        rwr AddAbGroup_Module_str_to_fiber_idp at h_eq,
        rwr AddAbGroup_Module_str_to_fiber_idp at h_eq,
        change h = _ at h_eq,
        have h_eq' : h.1.1.1.1.1.1 = 𝟙 (Set.mk M is_set_carrier), by rwr h_eq,
        fapply sigma.sigma_eq,
        { hinduction str₁ with ops₁ laws₁, hinduction str₂ with ops₂ laws₂,
          hinduction ops₁ with mul₁, hinduction ops₂ with mul₂,
          change Π r m, h.1.1.1.1.1.1 (mul₁ r m) = mul₂ r (h.1.1.1.1.1.1 m) at h_laws,
          fapply ap scal_ops_str.mk, apply eq_of_homotopy2, intros r m, 
          change _ = mul₂ r ((𝟙 (Set.mk M is_set_carrier) : M -> M) m),
          rwr <- h_eq', rwr <- h_laws, rwr h_eq' },         
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
      { intro h, exact is_prop.elim _ _ },
      { intro h, exact is_set.elim _ _ } } }
end

@[hott, instance]
def Module_is_cat (R : CommRing.{u}) : is_cat.{u u+1} (Module.{u} R) := 
  by apply_instance

@[hott]
def Module_Category (R : CommRing.{u}) : Category :=
  Category.mk (Module.{u} R) (Module_is_cat R)

/- For calculations with module homomorphisms, it is more effective to extract the laws
   of a homomorphism. -/

@[hott, reducible]
def Module_to_Set_functor (R : CommRing.{u}) : Module R ⥤ Set :=
begin
  apply λ F, concrete_forget_functor (@Module.to_AddAbGroup R) ⋙ F,
  apply λ F, concrete_forget_functor (AddAbGroup.to_AbGroup) ⋙ F,
  apply λ F, concrete_forget_functor (AbGroup.to_Group) ⋙ F,
  exact Group_to_Set_functor
end   

@[hott]
def Module_to_Set_map_comp (R : CommRing.{u}) {L M N : Module R} (f : L ⟶ M) (g : M ⟶ N) :
  Π (l : (Module_to_Set_functor R).obj L), 
       ((Module_to_Set_functor R).map f ≫ (Module_to_Set_functor R).map g) l =
        (Module_to_Set_functor R).map g ((Module_to_Set_functor R).map f l) := 
λ l, idp 

@[hott, instance]
def Module_Set_has_add (R : CommRing) (M : Module R) : 
  has_add ((Module_to_Set_functor R).obj M) :=
begin apply has_add.mk, change M -> M -> M, intros m₁ m₂, exact m₁ + m₂ end

@[hott, instance]
def Module_Set_has_zero (R : CommRing) (M : Module R) : 
  has_zero ((Module_to_Set_functor R).obj M) :=
begin apply has_zero.mk, change ↥M, exact 0 end

@[hott, instance]
def Module_Set_has_neg (R : CommRing) (M : Module R) : 
  has_neg ((Module_to_Set_functor R).obj M) :=
begin apply has_neg.mk, change M -> M, intro m, exact -m end  

@[hott, instance]
def Module_Set_has_act (R : CommRing) (M : Module R) : 
  has_act R ((Module_to_Set_functor R).obj M) :=
begin apply has_act.mk, change R -> M -> M, intros r m, exact r ⬝ m end
@[hott]  --[GEVE]

structure module_hom_str {R : CommRing} {M N : Module R} (f : M.carrier -> N.carrier) :=
  (add_comp : Π (m₁ m₂ : M), f (m₁ + m₂) = f m₁ + f m₂)
  (zero_comp : f 0 = 0)
  (scal_mul_comp : Π (r : R) (m : M), f (r ⬝ m) = r ⬝ f m)

@[hott]
def module_hom_laws {R : CommRing} {M N : Module R} (f : M ⟶ N) : 
  module_hom_str ((Module_to_Set_functor R).map f) :=
module_hom_str.mk f.1.1.1.1.1.1.2 f.1.1.1.1.2 f.2 

@[hott]  --[GEVE]
def module_hom.mk {R : CommRing} {M N : Module R} (f : M -> N) : 
  module_hom_str f -> (M ⟶ N) :=
λ str, ⟨⟨⟨⟨⟨⟨⟨f, str.add_comp⟩, true.intro⟩, str.zero_comp⟩, true.intro⟩, true.intro⟩, 
                             true.intro⟩, str.scal_mul_comp⟩ 

@[hott] 
def Module_to_Set_functor_is_faithful {R : CommRing} : 
  is_faithful_functor (Module_to_Set_functor R) :=
begin 
  fapply faithful_is_trans (concrete_forget_functor (Module.to_AddAbGroup)), 
  { apply @concrete_forget_functor_is_faithful _ _ Module.to_AddAbGroup },
  { fapply faithful_is_trans (concrete_forget_functor (AddAbGroup.to_AbGroup)), 
    { apply @concrete_forget_functor_is_faithful _ _ AddAbGroup.to_AbGroup },
    { fapply faithful_is_trans (concrete_forget_functor (AbGroup.to_Group)),
      { apply @concrete_forget_functor_is_faithful _ _ AbGroup.to_Group },
      { apply Group_to_Set_functor_is_faithful } } } 
end  

@[hott]
def module_sum_of_tuple_hom {R : CommRing} {M N : Module R} {n : ℕ} (h : M ⟶ N) :
  Π (m : tuple M n), (Module_to_Set_functor R).map h (module_sum_of_tuple m) = 
            module_sum_of_tuple (λ i : fin n, (Module_to_Set_functor R).map h (m i)) :=
begin
  hinduction n,
  { intro m, change (Module_to_Set_functor R).map h 0 = 0, 
    exact (module_hom_laws h).zero_comp },
  { intro m, change (Module_to_Set_functor R).map h (module_sum_of_tuple _ + _) = 
                    module_sum_of_tuple _ + (Module_to_Set_functor R).map _ _, 
    rwr (module_hom_laws h).add_comp, 
    apply ap (λ l : N, l + (Module_to_Set_functor R).map h 
                                           (m (fin.mk n (nat.le_refl (n + 1))))),
    rwr ih (@tuple.split_left _ n 1 m) }
end


end algebra

end hott