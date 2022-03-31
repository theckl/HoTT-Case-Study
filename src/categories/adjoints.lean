import categories.examples

universes v v' u u' w
hott_theory

namespace hott
open hott.is_trunc hott.set hott.categories

namespace categories.adjoints

/- There are two equivalent characterizations of adjoint functors. 

   The first definition relies on natural transformations of compositions of two
   functors to and from identity functors compatible by the zigzag equalities;
   the latter can be seen as equalities of natural transformation if we add 
   associativity and neutrality on the level of transformations at suitable places. 
   But this makes the formulas unwieldy and therefore we just record what the zigzag 
   relations look like on the level of homomorphisms. -/
@[hott]
structure adjoint_functors {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] (L : C ⥤ D) (R : D ⥤ C) :=
(unit : id_functor C ⟹ L ⋙ R)
(counit : R ⋙ L ⟹ id_functor D)
(zigzag_L : Π c : C, (tr_whisk_r unit L).app c ≫ (tr_whisk_l L counit).app c = 
                                                                         𝟙 (L.obj c))
            --tr_whisk_r unit L ≫ (assoc_funct_iso L R L).hom ≫ tr_whisk_l L counit = 
            --(l_neutral_funct_iso L).hom ≫ 𝟙 L ≫ (r_neutral_funct_iso L).inv)
(zigzag_R : Π d : D, (tr_whisk_l R unit).app d ≫ (tr_whisk_r counit R).app d = 
                                                                         𝟙 (R.obj d))
            --tr_whisk_l R unit ≫ (assoc_funct_iso R L R).inv ≫ tr_whisk_r counit R = 
            --(l_neutral_funct_iso R).hom ≫ 𝟙 R ≫ (r_neutral_funct_iso R).inv)                                      

@[hott]
structure is_left_adjoint {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] (L : C ⥤ D) := 
(R : D ⥤ C)  
(adj : adjoint_functors L R) 

@[hott]
structure is_right_adjoint {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] (R : C ⥤ D) := 
(L : D ⥤ C)  
(adj : adjoint_functors L R)

@[hott]
def right_adj_is_unique {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] (L : C ⥤ D) : is_prop (is_left_adjoint L) :=
begin 
  apply is_prop.mk, intros R_adj R_adj', 
  hinduction R_adj with R adj, hinduction R_adj' with R' adj', 
  hinduction adj with η ε zzL zzR, hinduction adj' with η' ε' zzL' zzR', fapply apd011, 
  { apply category.isotoid, fapply iso.mk, 
    { exact (r_neutral_funct_iso R).inv ≫ tr_whisk_l R η' ≫ 
            (assoc_funct_iso R L R').inv ≫ tr_whisk_r ε R' ≫ 
            (l_neutral_funct_iso R').hom },
    { exact (r_neutral_funct_iso R').inv ≫ tr_whisk_l R' η ≫ 
            (assoc_funct_iso R' L R).inv ≫ tr_whisk_r ε' R ≫ 
            (l_neutral_funct_iso R).hom },
    { apply nat_trans_eq, apply eq_of_homotopy, intro d,  
      change (𝟙 (R'.obj d) ≫ η.app (R'.obj d) ≫ 𝟙 (R.obj (L.obj (R'.obj d))) ≫ 
             R.map (ε'.app d) ≫ 𝟙 (R.obj d)) ≫ (𝟙 (R.obj d) ≫ η'.app (R.obj d) ≫ 
             𝟙 (R'.obj (L.obj (R.obj d))) ≫ R'.map (ε.app d) ≫ 𝟙 (R'.obj d)) = 
             𝟙 (R'.obj d), 
      repeat { rwr precategory.id_comp }, repeat { rwr precategory.comp_id },
      rwr <- precategory.assoc, rwr precategory.assoc (η.app (R'.obj d)), 
      change (_ ≫ (id_functor C).map (R.map (ε'.app d)) ≫ 
                   η'.app (R.obj ((id_functor D).obj d))) ≫ _ = _, 
      change (_ ≫ (tr_whisk_r (tr_whisk_r ε' R) (id_functor C)).app d ≫ 
                    (tr_whisk_l (id_functor D) (tr_whisk_l R η')).app d) ≫ _ = _,
      change (_ ≫ (tr_whisk_r (tr_whisk_r ε' R) (id_functor C) ≫ 
                    tr_whisk_l (id_functor D) (tr_whisk_l R η')).app d) ≫ _ = _,              
      rwr horiz_comp_eq (tr_whisk_r ε' R) (tr_whisk_l R η'),           
      sorry },
    { sorry } },
  { sorry }
end    

@[hott]
structure adjoint_functors_on_hom {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] (L : C ⥤ D) (R : D ⥤ C) :=
(hom_bij : Π (c : C) (d : D), bijection (L.obj c ⟶ d) (c ⟶ R.obj d)) 
(nat_L : Π {c : C} {d : D} {c' : C} (h : c' ⟶ c) (f : L.obj c ⟶ d), 
           hom_bij c' d (L.map h ≫ f) = h ≫ hom_bij c d f)
(nat_R : Π {c : C} {d : D} {d' : D} (g : d ⟶ d') (f : L.obj c ⟶ d), 
           hom_bij c d' (f ≫ g) = hom_bij c d f ≫ R.map g)                                               

@[hott]
def adjoint_to_adjoint_hom {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] {L : C ⥤ D} {R : D ⥤ C} : 
  adjoint_functors L R -> adjoint_functors_on_hom L R :=
begin 
  intro adj, fapply adjoint_functors_on_hom.mk, 
  { intros c d, fapply bijection.mk,                  --hom_bij
    { intro g, exact adj.trafo.app c ≫ R.map g },
    { fapply is_set_bijective.mk, 
      { intros g₁ g₂ p, rwr adj.uniq (adj.trafo.app c ≫ R.map g₂) g₁ p⁻¹,
        exact (adj.uniq (adj.trafo.app c ≫ R.map g₂) g₂ idp)⁻¹ },
      { intro f, fapply image.mk, exact (adj.hom f).1, exact (adj.hom f).2⁻¹ } } },
  { intros c d c' h f,       --nat_L
    calc _ = adj.trafo.app c' ≫ R.map (L.map h ≫ f) : idp
         ... = adj.trafo.app c' ≫ R.map (L.map h) ≫ R.map f : by rwr R.map_comp
         ... = (adj.trafo.app c' ≫ R.map (L.map h)) ≫ R.map f : by rwr precategory.assoc
         ... = (adj.trafo.app c' ≫ (L ⋙ R).map h) ≫ R.map f : idp
         ... = (h ≫ adj.trafo.app c) ≫ R.map f : by rwr <- adj.trafo.naturality h
         ... = h ≫ adj.trafo.app c ≫ R.map f : by rwr precategory.assoc
         ... = _ : idp },
  { intros c d d' g f,   --nat_R
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
def adjoint_hom_to_adjoint {C : Type u} {D : Type u'} [category.{v} C] 
  [category.{v'} D] {L : C ⥤ D} {R : D ⥤ C} : adjoint_functors_on_hom L R ->
  adjoint_functors L R :=
begin 
  intro adj, fapply adjoint_functors.mk,
  { fapply nat_trans.mk,      --trafo
    { intro c, exact adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) },
    { intros c c' f, 
      calc _ = f ≫ adj.hom_bij c' (L.obj c') (𝟙 (L.obj c')) : idp
           ... = adj.hom_bij c (L.obj c') (L.map f ≫ (𝟙 (L.obj c'))) :
                 by rwr <- adj.nat_L f (𝟙 (L.obj c'))
           ... = adj.hom_bij c (L.obj c') ((L.map f) ≫ 𝟙 (L.obj c')) : idp
           ... = adj.hom_bij c (L.obj c') (L.map f) : by rwr precategory.comp_id
           ... = adj.hom_bij c (L.obj c') (𝟙 (L.obj c) ≫ L.map f) : by rwr precategory.id_comp
           ... = _ : by rwr adj.nat_R (L.map f) (𝟙 (L.obj c)) } },
  { intros c d f, let g := inv_bijection_of (adj.hom_bij c d) f,  --hom
    have p : f = adj.hom_bij c d g, from (inv_bij_r_inv (adj.hom_bij c d) f)⁻¹,
    fapply sigma.mk, 
    { exact g },
    { change f = adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) ≫ R.map g, rwr p, 
      calc _ = (adj.hom_bij c d) (𝟙 (L.obj c) ≫ g) : by rwr precategory.id_comp
           ... = _ : by rwr adj.nat_R g (𝟙 (L.obj c)) } },
  { intros c d f g, 
    change f = adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) ≫ R.map g ->   --uniq
                                 g = inv_bijection_of (adj.hom_bij c d) f, intro p,
    apply bijection_l_to_r (adj.hom_bij c d),
    calc _ = (adj.hom_bij c d) (𝟙 (L.obj c) ≫ g) : by rwr precategory.id_comp
         ... = adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) ≫ R.map g :
               by rwr adj.nat_R g (𝟙 (L.obj c))
         ... = _ : by rwr <- p }  
end       

@[hott]
def adjoint_to_adjunction_eq {C : Type u} {D : Type u'} [precategory.{v} C] 
  [precategory.{v'} D] {L : C ⥤ D} {R : D ⥤ C} (adj : adjoint_functors_on_hom L R) 
  (c : C) : 
  (adjoint_hom_to_adjoint adj).trafo.app c = adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) := 
idp

end categories.adjoints

end hott