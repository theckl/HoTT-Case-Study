import categories.examples categories.subobj

universes v v' u u' w
hott_theory

namespace hott
open hott.is_trunc hott.set hott.precategories hott.categories

namespace categories.adjoints

/- There are two equivalent characterizations of adjoint functors. 

   The first definition relies on natural transformations of compositions of two
   functors to and from identity functors compatible by the zigzag equalities;
   the latter can be seen as equalities of natural transformation if we add 
   associativity and neutrality on the level of transformations at suitable places. 
   But this makes the formulas unwieldy and therefore we just record what the zigzag 
   relations look like on the level of homomorphisms. -/
@[hott]
structure adjoint_functors {C : Type u} {D : Type u'} [is_precat.{v} C] 
  [is_precat.{v'} D] (L : C ⥤ D) (R : D ⥤ C) :=
(unit : id_functor C ⟶ L ⋙ R)
(counit : R ⋙ L ⟶ id_functor D)
(zigzag_L : Π c : C, L.map (nat_trans.app unit c) ≫ 
                    @nat_trans.app _ _ _ _ (R ⋙ L) _ counit (L.obj c) = 𝟙 (L.obj c))
            --tr_whisk_r unit L ≫ (assoc_funct_iso L R L).hom ≫ tr_whisk_l L counit = 
            --(l_neutral_funct_iso L).hom ≫ 𝟙 L ≫ (r_neutral_funct_iso L).inv)
(zigzag_R : Π d : D, unit.app (R.obj d) ≫ R.map (counit.app d) = 𝟙 (R.obj d))
            --tr_whisk_l R unit ≫ (assoc_funct_iso R L R).inv ≫ tr_whisk_r counit R = 
            --(l_neutral_funct_iso R).hom ≫ 𝟙 R ≫ (r_neutral_funct_iso R).inv)                                      

@[hott]
structure is_left_adjoint {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L : C ⥤ D) := 
(R : D ⥤ C)  
(adj : adjoint_functors L R) 

@[hott]
structure is_right_adjoint {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (R : C ⥤ D) := 
(L : D ⥤ C)  
(adj : adjoint_functors L R)

@[hott]
def left_adjoint_iso {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L L' : C ⥤ D) (R : D ⥤ C) (adj : adjoint_functors L R)
  (adj' : adjoint_functors L' R) : L ⟶ L' :=
(l_neutral_funct_iso L).ih.inv ≫ tr_whisk_r adj'.unit L ≫ 
  (assoc_funct_iso L' R L).hom ≫ tr_whisk_l L' adj.counit ≫ 
  (r_neutral_funct_iso L').hom

@[hott]
def right_adjoint_iso {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L : C ⥤ D) (R R' : D ⥤ C) (adj : adjoint_functors L R)
  (adj' : adjoint_functors L R') : R ⟶ R' :=
(r_neutral_funct_iso R).ih.inv ≫ tr_whisk_l R adj'.unit ≫ 
  (assoc_funct_iso R L R').ih.inv ≫ tr_whisk_r adj.counit R' ≫ 
  (l_neutral_funct_iso R').hom  

@[hott]
def left_adjoint_iso_inv {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L L' : C ⥤ D) (R : D ⥤ C) (adj : adjoint_functors L R)
  (adj' : adjoint_functors L' R) : 
  left_adjoint_iso L L' R adj adj' ≫ left_adjoint_iso L' L R adj' adj = 𝟙 L :=   
begin
  let η := adj.unit, let η' := adj'.unit, let ε := adj.counit, let ε' := adj'.counit,
  apply nat_trans_eq, apply eq_of_homotopy, intro c,  
  change (𝟙 (L.obj c) ≫ L.map (η'.app c) ≫ 𝟙 (L.obj (R.obj (L'.obj c))) ≫ 
         (ε.app (L'.obj c)) ≫ 𝟙 (L'.obj c)) ≫ (𝟙 (L'.obj c) ≫ L'.map (η.app c) ≫ 
          𝟙 (L'.obj (R.obj (L.obj c))) ≫ ε'.app (L.obj c) ≫ 𝟙 (L.obj c)) = 
          𝟙 (L.obj c), 
  repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id },
  rwr <- is_precat.assoc, rwr is_precat.assoc (L.map (η'.app c)), 
  change (_ ≫ ε.app (L'.obj ((id_functor C).obj c)) ≫ 
               (id_functor D).map (L'.map (η.app c))) ≫ _ = _, 
  change (_ ≫ (tr_whisk_l (id_functor C) (tr_whisk_l L' ε) ≫ 
                tr_whisk_r η (L' ⋙ (id_functor D))).app c) ≫ _ = _,              
  rwr <- horiz_comp_eq η (tr_whisk_l L' ε),
  change (L.map (η'.app ((id_functor C).obj c)) ≫ L.map (R.map (L'.map (η.app c))) ≫
         ε.app (L'.obj (R.obj (L.obj c)))) ≫ (id_functor D).map (ε'.app (L.obj c)) = _,           
  rwr <- is_precat.assoc (L.map (η'.app ((id_functor C).obj c))), 
  rwr is_precat.assoc, rwr <- L.map_comp,
  change L.map ((tr_whisk_l (id_functor C) η' ≫ tr_whisk_r η (L' ⋙ R)).app c) ≫
         (tr_whisk_l (R ⋙ L') ε ≫ tr_whisk_r ε' (id_functor D)).app (L.obj c) = _,
  rwr <- horiz_comp_eq η η', rwr <- horiz_comp_eq ε' ε, 
  change L.map (η.app c ≫ η'.app (R.obj (L.obj c))) ≫ 
         L.map (R.map (ε'.app (L.obj c))) ≫ ε.app (L.obj c) = _,
  rwr <- is_precat.assoc, rwr <- L.map_comp, rwr is_precat.assoc (η.app c), 
  rwr adj'.zigzag_R, rwr is_precat.comp_id, rwr adj.zigzag_L
end  

@[hott]
def right_adjoint_iso_inv {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L : C ⥤ D) (R R' : D ⥤ C) (adj : adjoint_functors L R)
  (adj' : adjoint_functors L R') : 
  right_adjoint_iso L R R' adj adj' ≫ right_adjoint_iso L R' R adj' adj = 𝟙 R :=   
begin
  let η := adj.unit, let η' := adj'.unit, let ε := adj.counit, let ε' := adj'.counit,
  apply nat_trans_eq, apply eq_of_homotopy, intro d,  
  change (𝟙 (R.obj d) ≫ η'.app (R.obj d) ≫ 𝟙 (R'.obj (L.obj (R.obj d))) ≫ 
          R'.map (ε.app d) ≫ 𝟙 (R'.obj d)) ≫ (𝟙 (R'.obj d) ≫ η.app (R'.obj d) ≫ 
          𝟙 (R.obj (L.obj (R'.obj d))) ≫ R.map (ε'.app d) ≫ 𝟙 (R.obj d)) = 
          𝟙 (R.obj d), 
  repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id },
  rwr <- is_precat.assoc, rwr is_precat.assoc (η'.app (R.obj d)), 
  change (_ ≫ (id_functor C).map (R'.map (ε.app d)) ≫ 
               η.app (R'.obj ((id_functor D).obj d))) ≫ _ = _, 
  change (_ ≫ (tr_whisk_r (tr_whisk_r ε R') (id_functor C) ≫ 
              (tr_whisk_l ((id_functor D) ⋙ R') η)).app d) ≫ _ = _,              
  rwr horiz_comp_eq (tr_whisk_r ε R') η,
  change ((id_functor C).map (η'.app (R.obj d)) ≫ η.app (R'.obj (L.obj (R.obj d))) 
    ≫ R.map (L.map (R'.map (ε.app d)))) ≫ R.map (ε'.app ((id_functor D).obj d)) = _,           
  rwr <- is_precat.assoc (η'.app (R.obj d)), rwr is_precat.assoc, 
  rwr <- R.map_comp,
  change (tr_whisk_r η' (id_functor C) ≫ tr_whisk_l (L ⋙ R') η).app (R.obj d) ≫
          R.map ((tr_whisk_r ε (R' ⋙ L) ≫ tr_whisk_l (id_functor D) ε').app d) = _,
  rwr horiz_comp_eq η' η, rwr horiz_comp_eq ε ε', 
  change (η.app (R.obj d) ≫ R.map (L.map (η'.app (R.obj d)))) ≫ 
          R.map (ε'.app (L.obj (R.obj d)) ≫ ε.app d) = _, rwr R.map_comp,
  rwr is_precat.assoc (η.app (R.obj d)), 
  rwr <- is_precat.assoc _ _ (R.map (ε.app d)), rwr <- R.map_comp, rwr adj'.zigzag_L,
  rwr R.map_id, rwr is_precat.id_comp, rwr adj.zigzag_R
end  

@[hott]
def unit_tr_L {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L L' : C ⥤ D} {R : D ⥤ C} (p : L = L') 
  (η : id_functor C ⟶ L ⋙ R) : 
  p ▸[λ S, id_functor C ⟶ S ⋙ R] η = η ≫ (tr_whisk_r (idtoiso p).hom R) :=
begin hinduction p, hsimp, rwr tr_whisk_r_id, rwr is_precat.comp_id η end 

@[hott]
def unit_tr_R {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R R' : D ⥤ C} (p : R = R') 
  (η : id_functor C ⟶ L ⋙ R) : 
  p ▸[λ S, id_functor C ⟶ L ⋙ S] η = η ≫ (tr_whisk_l L (idtoiso p).hom) :=
begin hinduction p, hsimp, rwr tr_whisk_l_id, rwr is_precat.comp_id η end  

@[hott]
def counit_tr_L {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L L' : C ⥤ D} {R : D ⥤ C} (p : L = L') 
  (ε : R ⋙ L ⟶ id_functor D) : 
  p ▸[λ S, R ⋙ S ⟶ id_functor D] ε = (tr_whisk_l R (idtoiso p).ih.inv) ≫ ε :=
begin hinduction p, hsimp, rwr tr_whisk_l_id, rwr is_precat.id_comp ε end

@[hott]
def counit_tr_R {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R R' : D ⥤ C} (p : R = R') 
  (ε : R ⋙ L ⟶ id_functor D) : 
  p ▸[λ S, S ⋙ L ⟶ id_functor D] ε = (tr_whisk_r (idtoiso p).ih.inv L) ≫ ε :=
begin hinduction p, hsimp, rwr tr_whisk_r_id, rwr is_precat.id_comp ε end 

@[hott, instance]
def left_adj_is_unique {C : Type u} [is_precat C] {D : Type u'} [is_cat D] 
  (R : D ⥤ C) : is_prop (is_right_adjoint R) :=
begin 
  apply is_prop.mk, intros R_adj R_adj', 
  hinduction R_adj with L adj, hinduction R_adj' with L' adj', 
  fapply apd011, 
  { exact category.isotoid (iso.mk (left_adjoint_iso L L' R adj adj')
                        (is_iso.mk (left_adjoint_iso L' L R adj' adj)
                                   (left_adjoint_iso_inv L' L R adj' adj)
                                   (left_adjoint_iso_inv L L' R adj adj'))) },
  { hinduction adj with η ε zzL zzR, hinduction adj' with η' ε' zzL' zzR', 
    fapply apdo011111 (λ L, @adjoint_functors.mk _ _ _ _ L R) _, 
    { apply pathover_of_tr_eq, rwr unit_tr_L, 
      rwr @category.idtoiso_rinv' (C ⥤ D) _ _, 
      apply nat_trans_eq, apply eq_of_homotopy, intro c,
      change η.app c ≫ R.map (𝟙 (L.obj c) ≫ L.map (η'.app c) ≫ 𝟙 (L.obj (R.obj (L'.obj c))) ≫ 
         (ε.app (L'.obj c)) ≫ 𝟙 (L'.obj c)) = _, 
      repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id }, 
      rwr R.map_comp, rwr <- is_precat.assoc, 
      change (η.app ((id_functor C).obj c) ≫ (L ⋙ R).map (η'.app c)) ≫ _ = _, 
      change (tr_whisk_l (id_functor C) η ≫ tr_whisk_r η' (L ⋙ R)).app c ≫ _ = _,
      rwr <- horiz_comp_eq η' η, 
      change (η'.app c ≫ η.app (R.obj (L'.obj c))) ≫ _ = _,
      rwr is_precat.assoc, rwr zzR, rwr is_precat.comp_id },
    { apply pathover_of_tr_eq, rwr counit_tr_L, 
      rwr @category.idtoiso_rinv' (C ⥤ D) _ _, 
      apply nat_trans_eq, apply eq_of_homotopy, intro d, 
      change (𝟙 (L'.obj (R.obj d)) ≫ L'.map (η.app (R.obj d)) ≫ 
             𝟙 (L'.obj (R.obj (L.obj (R.obj d)))) ≫ ε'.app (L.obj (R.obj d)) ≫ 
             𝟙 (L.obj (R.obj d))) ≫ ε.app d = _,
      repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id },        
      rwr is_precat.assoc,    
      change _ ≫ ε'.app ((R ⋙ L).obj d) ≫ (id_functor D).map (ε.app d) = _,
      change _ ≫ (tr_whisk_l (R ⋙ L) ε' ≫ tr_whisk_r ε (id_functor D)).app d = _,
      rwr <- horiz_comp_eq ε ε',
      change _ ≫ L'.map (R.map (ε.app d)) ≫ ε'.app d = _, rwr <- is_precat.assoc,
      rwr <- L'.map_comp, rwr zzR, rwr L'.map_id, rwr is_precat.id_comp },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end   

@[hott, instance]
def right_adj_is_unique {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) : is_prop (is_left_adjoint L) :=
begin 
  apply is_prop.mk, intros R_adj R_adj', 
  hinduction R_adj with R adj, hinduction R_adj' with R' adj', 
  fapply apd011, 
  { exact @category.isotoid (D ⥤ C) _ _ _
              (iso.mk (right_adjoint_iso L R R' adj adj')
                      (is_iso.mk   (right_adjoint_iso L R' R adj' adj)
                                   (right_adjoint_iso_inv L R' R adj' adj)
                                   (right_adjoint_iso_inv L R R' adj adj'))) },
  { hinduction adj with η ε zzL zzR, hinduction adj' with η' ε' zzL' zzR', 
    fapply apdo011111 (@adjoint_functors.mk _ _ _ _ L) _, 
    { apply pathover_of_tr_eq, rwr unit_tr_R, 
      rwr @category.idtoiso_rinv' (D ⥤ C) _ _, 
      apply nat_trans_eq, apply eq_of_homotopy, intro c,
      change η.app c ≫ ((𝟙 (R.obj (L.obj c)) ≫ η'.app (R.obj (L.obj c)) ≫ 
             𝟙 (R'.obj (L.obj (R.obj (L.obj c)))) ≫ R'.map (ε.app (L.obj c)) ≫ 
             𝟙 (R'.obj (L.obj c)))) = _, 
      repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id }, 
      rwr <- is_precat.assoc, 
      change ((id_functor C).map (η.app c) ≫ η'.app ((L ⋙ R).obj c)) ≫ _ = _, 
      change (tr_whisk_r η (id_functor C) ≫ tr_whisk_l (L ⋙ R) η').app c ≫ _ = _,
      rwr horiz_comp_eq η η', 
      change (η'.app ((id_functor C).obj c) ≫ R'.map (L.map (η.app c))) ≫ _ = _,
      rwr is_precat.assoc, rwr <- R'.map_comp, rwr zzL, rwr R'.map_id, 
      rwr is_precat.comp_id },
    { apply pathover_of_tr_eq, rwr counit_tr_R, 
      rwr @category.idtoiso_rinv' (D ⥤ C) _ _, 
      apply nat_trans_eq, apply eq_of_homotopy, intro d, 
      change (L.map (𝟙 (R'.obj d) ≫ η.app (R'.obj d) ≫ 𝟙 (R.obj (L.obj (R'.obj d))) ≫
              R.map (ε'.app d) ≫ 𝟙 (R.obj d))) ≫ ε.app d = _,
      repeat { rwr is_precat.id_comp }, repeat { rwr is_precat.comp_id },        
      rwr L.map_comp, rwr is_precat.assoc,    
      change _ ≫ (R ⋙ L).map (ε'.app d) ≫ ε.app ((id_functor D).obj d) = _,
      change _ ≫ (tr_whisk_r ε' (R ⋙ L) ≫ tr_whisk_l (id_functor D) ε).app d = _,
      rwr horiz_comp_eq ε' ε,
      change _ ≫ ε.app (L.obj (R'.obj d)) ≫ ε'.app d = _, 
      rwr <- is_precat.assoc,
      rwr zzL, rwr is_precat.id_comp },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end    

@[hott]
class has_right_adjoint {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) :=
(l_adj : is_left_adjoint L)

@[hott, instance]
def has_right_adj_is_prop {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) : is_prop (has_right_adjoint L) :=
begin 
  apply is_prop.mk, intros hra₁ hra₂, hinduction hra₁, hinduction hra₂,
  apply ap has_right_adjoint.mk, exact is_prop.elim _ _ 
end

@[hott]
def right_adjoint_of {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) [H : has_right_adjoint L] : D ⥤ C :=
H.l_adj.R  

@[hott]
def adjoint_right_adjoint_of {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) [H : has_right_adjoint L] : 
  adjoint_functors L (right_adjoint_of L) :=
H.l_adj.adj

@[hott]
class has_left_adjoint {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (R : D ⥤ C) :=
(r_adj : is_right_adjoint R)

@[hott]
def left_adjoint_of {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (R : D ⥤ C) [H : has_left_adjoint R] : C ⥤ D :=
H.r_adj.L 

@[hott]
def adjoint_left_adjoint_of {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (R : D ⥤ C) [H : has_left_adjoint R] : 
  adjoint_functors (left_adjoint_of R) R :=
H.r_adj.adj

@[hott]
class has_right_adjoints (C : Type u) (D : Type u') [is_cat C] 
  [is_precat D] :=
(has_r_adj : Π L : C ⥤ D, has_right_adjoint L)

@[hott, instance]
def has_right_adj_of_has_right_adjs {C : Type u} {D : Type u'} 
  [is_cat C] [is_precat D] [H : has_right_adjoints C D] 
  (L : C ⥤ D) : has_right_adjoint L :=
has_right_adjoints.has_r_adj L  

@[hott]
class has_left_adjoints (C : Type u) (D : Type u') [is_precat C] 
  [is_precat D] :=
(has_l_adj : Π R : D ⥤ C, has_left_adjoint R)

@[hott, instance]
def has_left_adj_of_has_left_adjs {C : Type u} {D : Type u'} 
  [is_precat C] 
  [is_precat D] [H : has_left_adjoints C D] (R : D ⥤ C) : has_left_adjoint R :=
has_left_adjoints.has_l_adj R 

@[hott]
class is_adjoint_functors {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (L : C ⥤ D) (R : D ⥤ C) := 
(is_adj : adjoint_functors L R) 

@[hott, instance]
def is_adj_of_has_right_adj {C : Type u} {D : Type u'} [is_cat C] 
  [is_precat D] (L : C ⥤ D) [H : has_right_adjoint L] : 
  is_adjoint_functors L H.l_adj.R :=
is_adjoint_functors.mk H.l_adj.adj

@[hott, instance]
def is_adj_of_has_left_adj {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] (R : D ⥤ C) [H : has_left_adjoint R] : 
  is_adjoint_functors H.r_adj.L R :=
is_adjoint_functors.mk H.r_adj.adj


/- Adjointness can also be characterized by bijections between sets of homomorphisms. 
   We first construct these bijections and their naturality from adjoint functors, 
   then we show how these bijections imply adjointness when they are natural. -/
@[hott]
def right_adj_hom {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R : D ⥤ C} [H : is_adjoint_functors L R] 
  {c : C} {d : D} (f : c ⟶ R.obj d) : L.obj c ⟶ d :=
L.map f ≫ H.is_adj.counit.app d    

@[hott]
def left_adj_hom {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R : D ⥤ C} [H : is_adjoint_functors L R] 
  {c : C} {d : D} (g : L.obj c ⟶ d) : c ⟶ R.obj d :=
H.is_adj.unit.app c ≫ R.map g  

@[hott]
structure adjoint_functors_on_hom {C : Type u} {D : Type u'} 
  [is_precat C] [is_precat D] (L : C ⥤ D) (R : D ⥤ C) :=
(hom_bij : Π (c : C) (d : D), bijection (L.obj c ⟶ d) (c ⟶ R.obj d)) 
(nat_L : Π {c : C} {d : D} {c' : C} (h : c' ⟶ c) (f : L.obj c ⟶ d), 
           hom_bij c' d (L.map h ≫ f) = h ≫ hom_bij c d f)
(nat_R : Π {c : C} {d : D} {d' : D} (g : d ⟶ d') (f : L.obj c ⟶ d), 
           hom_bij c d' (f ≫ g) = hom_bij c d f ≫ R.map g)                                               

@[hott]
def adjoint_to_adjoint_hom {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R : D ⥤ C} : 
  adjoint_functors L R -> adjoint_functors_on_hom L R :=
begin 
  intro adj, fapply adjoint_functors_on_hom.mk, 
  { intros c d, fapply has_inverse_to_bijection,    --hom_bij
    { intro g, exact adj.unit.app c ≫ R.map g },
    { intro f, exact L.map f ≫ adj.counit.app d },
    { fapply is_set_inverse_of.mk, 
      { intro f, hsimp, rwr <- is_precat.assoc, rwr <- adj.unit.naturality, 
        rwr is_precat.assoc, rwr adj.zigzag_R, rwr is_precat.comp_id },
      { intro g, hsimp, rwr adj.counit.naturality, rwr <- is_precat.assoc, 
        rwr adj.zigzag_L, rwr is_precat.id_comp } } },
  { intros c d c' h f,       --nat_L
    calc _ = adj.unit.app c' ≫ R.map (L.map h ≫ f) : idp
         ... = adj.unit.app c' ≫ R.map (L.map h) ≫ R.map f : 
               by rwr R.map_comp
         ... = (adj.unit.app c' ≫ R.map (L.map h)) ≫ R.map f : 
               by rwr is_precat.assoc
         ... = (adj.unit.app c' ≫ (L ⋙ R).map h) ≫ R.map f : idp
         ... = (h ≫ adj.unit.app c) ≫ R.map f : by rwr <- adj.unit.naturality h
         ... = h ≫ adj.unit.app c ≫ R.map f : by rwr is_precat.assoc
         ... = _ : idp },
  { intros c d d' g f,   --nat_R
    calc _ = adj.unit.app c ≫ R.map (f ≫ g) : idp
         ... = adj.unit.app c ≫ R.map f ≫ R.map g : by rwr R.map_comp
         ... = (adj.unit.app c ≫ R.map f) ≫ R.map g : by rwr is_precat.assoc
         ... = _ : idp } 
end

@[hott]
def adjoint_hom_to_adjoint {C : Type u} {D : Type u'} [is_precat C] 
  [is_precat D] {L : C ⥤ D} {R : D ⥤ C} : adjoint_functors_on_hom L R ->
  adjoint_functors L R :=
begin 
  intro adj, 
  have nat_L' : Π {c : C} {d : D} (f : c ⟶ R.obj d),
                    (inv_bijection_of (adj.hom_bij c d)).map f = L.map f ≫ 
                    (inv_bijection_of (adj.hom_bij (R.obj d) d)).map (𝟙 (R.obj d)), from
    begin 
      intros c d f, apply (adj.hom_bij c d).bij.inj, change (adj.hom_bij c d).map _ = _, 
      rwr inv_bij_r_inv (adj.hom_bij c d), change f = (adj.hom_bij c d) _, 
      rwr adj.nat_L f, change f = f ≫ (adj.hom_bij (R.obj d) d).map _, 
      rwr inv_bij_r_inv (adj.hom_bij (R.obj d) d), rwr is_precat.comp_id 
    end,               
  have nat_R' : Π {c : C} {d d' : D} (g : d ⟶ d') (f : c ⟶ R.obj d), 
                    inv_bijection_of (adj.hom_bij c d) f ≫ g = 
                    inv_bijection_of (adj.hom_bij c d') (f ≫ R.map g), from
    begin
      intros c d d' g f, apply (adj.hom_bij c d').bij.inj, 
      change _ = (adj.hom_bij c d').map ((inv_bijection_of (adj.hom_bij c d')).map _) , 
      rwr inv_bij_r_inv (adj.hom_bij c d'),
      change (adj.hom_bij c d') _ = _, rwr adj.nat_R, 
      change (adj.hom_bij c d).map ((inv_bijection_of (adj.hom_bij c d)).map f) ≫ _ = _, 
      rwr inv_bij_r_inv
    end, 
  have hom_map : Π {c : C} {d : D} (g : L.obj c ⟶ d), adj.hom_bij c d g =
                   adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) ≫ R.map g, from
    begin intros c d g, rwr <- adj.nat_R, rwr is_precat.id_comp end, 
  fapply adjoint_functors.mk,
  { fapply nat_trans.mk,      --unit
    { intro c, exact adj.hom_bij c (L.obj c) (𝟙 (L.obj c)) },
    { intros c c' f, 
      calc _ = f ≫ adj.hom_bij c' (L.obj c') (𝟙 (L.obj c')) : idp
           ... = adj.hom_bij c (L.obj c') (L.map f ≫ (𝟙 (L.obj c'))) :
                 by rwr <- adj.nat_L f (𝟙 (L.obj c'))
           ... = adj.hom_bij c (L.obj c') ((L.map f) ≫ 𝟙 (L.obj c')) : idp
           ... = adj.hom_bij c (L.obj c') (L.map f) : by rwr is_precat.comp_id
           ... = adj.hom_bij c (L.obj c') (𝟙 (L.obj c) ≫ L.map f) : 
                 by rwr is_precat.id_comp
           ... = _ : by rwr adj.nat_R (L.map f) (𝟙 (L.obj c)) } },
  { fapply nat_trans.mk,      --counit
    { intro d, exact inv_bijection_of (adj.hom_bij (R.obj d) d) (𝟙 (R.obj d)) },
    { intros d d' g, rwr nat_R', rwr is_precat.id_comp, 
      change L.map (R.map g) ≫ (inv_bijection_of (adj.hom_bij (R.obj d') d')).map _ = _, 
      rwr <- nat_L' (R.map g) } },         
  { intro c, change L.map ((adj.hom_bij c (L.obj c)).map (𝟙 (L.obj c))) ≫    --zigzag_L
        (inv_bijection_of (adj.hom_bij (R.obj (L.obj c)) (L.obj c))).map (𝟙 (R.obj _)) = _, 
    rwr <- nat_L', rwr inv_bij_l_inv }, 
  { intro d, change adj.hom_bij (R.obj d) (L.obj (R.obj d)) (𝟙 (L.obj (R.obj d))) ≫
                R.map (inv_bijection_of (adj.hom_bij (R.obj d) d) (𝟙 (R.obj d))) = _, 
    rwr <- hom_map, change (adj.hom_bij (R.obj d) d).map ((inv_bijection_of (adj.hom_bij 
                                                                (R.obj d) d)).map _) = _, 
    rwr inv_bij_r_inv }  --zigzag_R 
end       

/- `adjoint_functors_on_hom` is also a proposition if `C` and `D` are categories, so the 
   two ways of defining adjoint functors are logically equivalent. -/

/- In general, it is not clear how subobjects of `R.obj d` and `d` are connected, for a 
   functor `R : D ⥤ C` (for example, this is important when `R` is a forgetful functor of 
   structures). If `R` is right adjoint to `L : C ⥤ D`, subobjects of `d` yield subobjects of 
   `R.obj d`, by applying `R`. If in addition `R` is faithful, counits are isomorphisms and 
   units on subobjects of `R`-images are isomorphisms (in particular, subobjects of 
   `R`-images are `R`-images themselves), this is actually a 1-1 correspondence. -/  
@[hott]
def subobj_to_adjoint_subobj {C : Type _} [is_cat C] {D : Type _} [is_cat D] {L : C ⥤ D} {R : D ⥤ C} 
  (adj : adjoint_functors_on_hom L R) : Π (d : D), subobject d -> subobject (R.obj d) :=
begin
  intros d d', fapply subobject.mk (R.obj d'.obj) (R.map d'.hom),
  intros c f g hom_eq, apply (inv_bijection_of (adj.hom_bij c d'.obj)).bij.inj, 
  apply d'.is_mono, apply (adj.hom_bij c d).bij.inj, 
  change (adj.hom_bij c d) ((inv_bijection_of (adj.hom_bij c d'.obj)) _ ≫ _) = 
         (adj.hom_bij c d) ((inv_bijection_of (adj.hom_bij c d'.obj)) _ ≫ _), 
  rwr adj.nat_R, rwr adj.nat_R, rwr (inv_bij_is_inv (adj.hom_bij c d'.obj)).r_inv,
  rwr (inv_bij_is_inv (adj.hom_bij c d'.obj)).r_inv, exact hom_eq
end

@[hott]
def adjoint_subobj_to_subobj {C : Type _} [is_cat C] {D : Type _} [is_cat D] {L : C ⥤ D} {R : D ⥤ C} 
  (adj : adjoint_functors_on_hom L R) (Rff : @is_faithful_functor _ _ _ _ R)
  (adj_iso : Π (d : D) (c : subobject (R.obj d)), 
                     is_iso ((adj.hom_bij c.obj (L.obj c.obj)).map (𝟙 (L.obj c.obj)))) (d : D) : 
  subobject (R.obj d) -> subobject d :=
begin
  intro c, fapply subobject.mk (L.obj c.obj) (inv_bijection_of (adj.hom_bij c.obj d) c.hom),
  intros d' f g hom_eq, apply Rff, apply iso_rcancel (inv_iso (iso.mk _ (adj_iso d c))),
  apply c.is_mono,
  have p : c.hom = (adj.hom_bij c.obj (L.obj c.obj)).map (𝟙 (L.obj c.obj)) ≫ 
                     R.map (inv_bijection_of (adj.hom_bij c.obj d) c.hom), from 
  begin 
    change _ = (adj.hom_bij c.obj (L.obj c.obj)) (𝟙 (L.obj c.obj)) ≫ _,
    rwr <- adj.nat_R, rwr is_precat.id_comp, 
    change c.hom = (adj.hom_bij c.obj d).map ((inv_bijection_of (adj.hom_bij c.obj d)).map _), 
    rwr inv_bij_r_inv 
  end,
  rwr p, rwr is_precat.assoc, rwr is_precat.assoc (R.map g), 
  rwr <- is_precat.assoc _ _ (R.map ((inv_bijection_of (adj.hom_bij c.obj d)) c.hom)),
  change _ ≫ ((adj_iso d c).inv ≫ _) ≫ _ = _ ≫ ((adj_iso d c).inv ≫ _) ≫ _,
  rwr is_iso.r_inv (adj_iso d c), rwr is_precat.id_comp, rwr <- functor.map_comp,
  rwr <- functor.map_comp, exact ap (precategories.functor.map R) hom_eq
end 

@[hott]
def adjoint_subobjects_rinv {C : Type _} [is_cat C] {D : Type _} [is_cat D] {L : C ⥤ D} {R : D ⥤ C} : 
  Π (adj : adjoint_functors_on_hom L R) (Rff : is_faithful_functor R)
    (iso_adj_L : Π (d : D) (c : subobject (R.obj d)), 
                                           is_iso ((adj.hom_bij c.obj (L.obj c.obj)).map (𝟙 (L.obj c.obj)))), 
  Π (d : D) (c : subobject (R.obj d)), 
    subobj_to_adjoint_subobj adj d (adjoint_subobj_to_subobj adj @Rff iso_adj_L d c) = c :=
begin
  intros adj Rff iso_adj_L d c, apply eq.inverse, fapply iso_mono_to_equal_subobj, fapply iso_of_monos.mk,
  { change c.obj ≅ R.obj (L.obj c.obj), exact iso.mk _ (iso_adj_L d c) },
  { change (adj.hom_bij c.obj (L.obj c.obj)) (𝟙 (L.obj c.obj)) ≫ 
               R.map (inv_bijection_of (adj.hom_bij c.obj d) c.hom) = _, 
    rwr <- adj.nat_R, rwr is_precat.id_comp, 
    change (adj.hom_bij c.obj d).map ((inv_bijection_of (adj.hom_bij c.obj d)).map _) = _, 
    rwr inv_bij_r_inv  }
end

@[hott]
def adjoint_subobjects_linv {C : Type _} [is_cat C] {D : Type _} [is_cat D] {L : C ⥤ D} {R : D ⥤ C} : 
  Π (adj : adjoint_functors_on_hom L R) (Rff : is_faithful_functor R)
    (iso_adj_L : Π (d : D) (c : subobject (R.obj d)), 
                     is_iso ((adj.hom_bij c.obj (L.obj c.obj)).map (𝟙 (L.obj c.obj)))) 
    (iso_adj_R : Π (d : D), is_iso (inv_bijection_of (adj.hom_bij (R.obj d) d) (𝟙 (R.obj d)))),
  Π (d : D) (d' : subobject d), 
    adjoint_subobj_to_subobj adj @Rff iso_adj_L d (subobj_to_adjoint_subobj adj d d') = d' :=
begin
  intros adj Rff iso_adj_L iso_adj_R d d', fapply iso_mono_to_equal_subobj, fapply iso_of_monos.mk,
  { change L.obj (R.obj d'.obj) ≅ d'.obj, exact iso.mk _ (iso_adj_R d'.obj) },
  { change (inv_bijection_of (adj.hom_bij (R.obj d'.obj) d'.obj)) (𝟙 (R.obj d'.obj)) ≫ _ =
               (inv_bijection_of (adj.hom_bij (R.obj d'.obj) d)) (R.map d'.hom),
    apply (adj.hom_bij (R.obj d'.obj) d).bij.inj, 
    change (adj.hom_bij (R.obj d'.obj) d) ((inv_bijection_of (adj.hom_bij (R.obj d'.obj) 
                                                      d'.obj)) (𝟙 (R.obj d'.obj)) ≫ d'.hom) =
               (adj.hom_bij (R.obj d'.obj) d).map ((inv_bijection_of (adj.hom_bij 
                                                      (R.obj d'.obj) d)).map (R.map d'.hom)),
    rwr inv_bij_r_inv, rwr adj.nat_R, 
    change (adj.hom_bij (R.obj d'.obj) d'.obj).map 
                     ((inv_bijection_of (adj.hom_bij (R.obj d'.obj) d'.obj)).map _) ≫ _ = _,
    rwr inv_bij_r_inv, rwr is_precat.id_comp }
end

@[hott]
def adjoint_subobjects {C : Type _} [is_cat C] {D : Type _} [is_cat D] {L : C ⥤ D} {R : D ⥤ C} : 
  Π (adj : adjoint_functors_on_hom L R), is_faithful_functor R ->
    (Π (d : D) (c : subobject (R.obj d)), 
                     is_iso ((adj.hom_bij c.obj (L.obj c.obj)).map (𝟙 (L.obj c.obj)))) -> 
    (Π (d : D), is_iso (inv_bijection_of (adj.hom_bij (R.obj d) d) (𝟙 (R.obj d)))) ->
  Π (d : D), set.bijection (set.to_Set (subobject d)) (set.to_Set (subobject (R.obj d))) :=
begin
  intros adj Rff iso_adj_L iso_adj_R d, fapply has_inverse_to_bijection,
  { exact subobj_to_adjoint_subobj adj d },
  { apply adjoint_subobj_to_subobj adj @Rff iso_adj_L },
  { fapply is_set_inverse_of.mk,
    { exact adjoint_subobjects_rinv adj @Rff iso_adj_L d },
    { exact adjoint_subobjects_linv adj @Rff iso_adj_L iso_adj_R d } }
end

end categories.adjoints

end hott