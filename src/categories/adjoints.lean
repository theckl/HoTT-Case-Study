import categories.examples

universes v v' u u' w
hott_theory

namespace hott
open hott.set hott.categories

namespace categories.adjoints

/- It would be nice to denote these pullbacks by `f*` and `f_*`, but these notations
   would clash with others. -/
@[hott]
def pb_comp_hom {C : Type u} [precategory.{v} C] {c c' d : C} (f : c' ⟶ c) :
  (c ⟶ d) -> (c' ⟶ d) := λ h : c ⟶ d, f ≫ h

@[hott]
def pf_comp_hom {C : Type u} [precategory.{v} C] {c d d' : C} (f : d ⟶ d') :
  (c ⟶ d) -> (c ⟶ d') := λ h : c ⟶ d, h ≫ f

/- There are two equivalent characterizations of adjoint functors. -/
@[hott]
structure adjoint_functors {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] (L : C ⥤ D) (R : D ⥤ C) :=
(trafo : id_functor C ⟹ L ⋙ R)
(hom : Π {c : C} {d : D} (f : c ⟶ R.obj d), 
                                Σ (g : L.obj c ⟶ d), f = trafo.app c ≫ R.map g)
(uniq : Π {c : C} {d : D} (f : c ⟶ R.obj d) (g : L.obj c ⟶ d), 
                                f = trafo.app c ≫ R.map g -> g = (hom f).1)                                      

@[hott]
structure adjoint_functors_on_hom {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] (L : C ⥤ D) (R : D ⥤ C) :=
(hom_bij : Π (c : C) (d : D), bijection (L.obj c ⟶ d) (c ⟶ R.obj d)) 
(nat_L : Π (c : C) (d : D) (c' : C) (h : c' ⟶ c), 
           (hom_bij c' d) ∘ (pb_comp_hom (L.map h)) = (pb_comp_hom h) ∘ (hom_bij c d))
(nat_R : Π (c : C) (d : D) (d' : D) (g : d ⟶ d'), 
           (hom_bij c d') ∘ (pf_comp_hom g) = (pf_comp_hom (R.map g)) ∘ (hom_bij c d))                                               

@[hott]
def adjoint_to_adjoint_hom {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] {L : C ⥤ D} {R : D ⥤ C} : 
  adjoint_functors L R -> adjoint_functors_on_hom L R :=
begin 
  intro adj, fapply adjoint_functors_on_hom.mk, 
  { intros c d, fapply bijection.mk, 
    { intro g, exact adj.trafo.app c ≫ R.map g },
    { fapply is_set_bijective.mk, 
      { intros g₁ g₂ p, rwr adj.uniq (adj.trafo.app c ≫ R.map g₂) g₁ p⁻¹,
        exact (adj.uniq (adj.trafo.app c ≫ R.map g₂) g₂ idp)⁻¹ },
      { intro f, fapply image.mk, exact (adj.hom f).1, exact (adj.hom f).2⁻¹ } } },
  { intros c d c' h, apply eq_of_homotopy, intro f, 
    calc _ = adj.trafo.app c' ≫ R.map (L.map h ≫ f) : idp
         ... = adj.trafo.app c' ≫ R.map (L.map h) ≫ R.map f : by rwr R.map_comp
         ... = (adj.trafo.app c' ≫ R.map (L.map h)) ≫ R.map f : by rwr precategory.assoc
         ... = (adj.trafo.app c' ≫ (L ⋙ R).map h) ≫ R.map f : idp
         ... = (h ≫ adj.trafo.app c) ≫ R.map f : by rwr <- adj.trafo.naturality h
         ... = h ≫ adj.trafo.app c ≫ R.map f : by rwr precategory.assoc
         ... = _ : idp },
  { intros c d d' g, apply eq_of_homotopy, intro f, 
    calc _ = adj.trafo.app c ≫ R.map (f ≫ g) : idp
         ... = adj.trafo.app c ≫ R.map f ≫ R.map g : by rwr R.map_comp
         ... = (adj.trafo.app c ≫ R.map f) ≫ R.map g : by rwr precategory.assoc
         ... = _ : idp } 
end

@[hott]
def adjoint_to_adjoint_hom_eq (C : Type u) (D : Type u') [precategory.{v} C] 
  [precategory.{v'} D] {L : C ⥤ D} {R : D ⥤ C} (adj : adjoint_functors L R) {c : C} 
  {d : D} (g : L.obj c ⟶ d) : 
  (adjoint_to_adjoint_hom adj).hom_bij c d g = adj.trafo.app c ≫ R.map g := idp 

@[hott]
def adjoint_hom_to_adjoint {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] {L : C ⥤ D} {R : D ⥤ C} : adjoint_functors_on_hom L R ->
  adjoint_functors L R :=
begin 
  intro adj, fapply adjoint_functors.mk,
  { fapply nat_trans.mk, 
    { intro c, exact adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) },
    { intros c c' f, 
      calc _ = (pb_comp_hom f ∘ (adj.hom_bij c' (L.obj c'))) (𝟙 (L.obj c')) : idp
           ... = adj.hom_bij c (L.obj c') (L.map f) ≫ 𝟙 (R.obj (L.obj c')) : 
                 by rwr <- ap10 (adj.nat_L c' (L.obj c') c f) (𝟙 (L.obj c'))
           ... = _ : sorry } },
  { sorry },
  { sorry }
end       

@[hott]
def adjoint_to_adjunction_eq {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] {L : C ⥤ D} {R : D ⥤ C} (adj : adjoint_functors_on_hom L R) 
  (c : C) : 
  (adjoint_hom_to_adjoint adj).trafo.app c = adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) := 
idp

end categories.adjoints

end hott