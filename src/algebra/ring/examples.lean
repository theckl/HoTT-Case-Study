import algebra.ring.module 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

@[hott]  --[GEVE]
def zero_Module (R : CommRing) : Module R :=
begin  
  fapply Module.mk One, 
  fapply module.mk,
  { exact unit_AbGroup.struct },
  { intros r m, exact m },
  { intro m, exact idp },
  { intros r s m, exact idp },
  { intros r m n, exact idp },
  { intros r s m, change m = @ab_group.mul _ unit_AbGroup.struct m m, 
    hinduction m, exact @ab_group.mul_one _ unit_AbGroup.struct _ }
end

notation `[0]_` R := zero_Module R

@[hott]
def initial_mod_hom {R : CommRing} (M : Module R) : ([0]_R) ⟶ M :=
begin 
  fapply module_hom.mk,
  { intro o, exact 0 },
  { fapply module_hom_str.mk, 
    { intros o₁ o₂, rwr (module_laws M).add_zero },
    { exact idp },
    { intros r o, rwr scal_mul_zero_zero } } 
end

@[hott]
def initial_mod_hom_is_unique {R : CommRing} (M : Module R) : 
  Π (f g : ([0]_R) ⟶ M), f = g :=
begin 
  intros f g, fapply Module_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro o, 
  have p : Π (o : ([0]_R)), o = 0, from 
    begin intro o, hinduction o, exact idp end,
  rwr p o, exact eq.concat (module_hom_laws f).zero_comp (module_hom_laws g).zero_comp⁻¹
end

@[hott]
def terminal_mod_hom {R : CommRing} (M : Module R) : M ⟶ ([0]_R) :=
begin 
  fapply module_hom.mk,
  { intro m, exact 0 },
  { fapply module_hom_str.mk, 
    { intros m₁ m₂, rwr (module_laws ([0]_R)).add_zero },
    { exact idp },
    { intros r m, rwr scal_mul_zero_zero } } 
end

@[hott]
def terminal_mod_hom_is_unique {R : CommRing} (M : Module R) : 
  Π (f g : M ⟶ ([0]_R)), f = g :=
begin 
  intros f g, fapply Module_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro m, 
  have p : Π (o : ([0]_R)), o = 0, from 
    begin intro o, hinduction o, exact idp end,
  rwr p ((Module_to_Set_functor R).map g m), rwr p ((Module_to_Set_functor R).map f m) 
end

end algebra

end hott