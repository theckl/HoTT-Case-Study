import categories.subcat categories.diagrams 

universes v v' u u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.is_equiv hott.set hott.subset 
     hott.precategories hott.categories hott.categories.strict

/- We introduce limits of diagrams mapped to categories, by using cones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace categories.limits

@[hott]
structure cone {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] (F : J ⥤ C) :=
(X : C)
(π : (@constant_functor J _ C _ X) ⟹ F)

@[hott, reducible, hsimp]
def cone.leg {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] {F : J ⥤ C} (cF : cone F) : 
  Π j : J, cF.X ⟶ F.obj j := 
begin intro j, exact cF.π.app j end

@[hott]
def cone.fac {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} (s : cone F) : 
  ∀ {j k : J} (f : j ⟶ k), s.π.app j ≫ F.map f = s.π.app k :=
begin intros j k f, rwr <- s.π.naturality f, hsimp end   

@[hott]
def cone_eq {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] {F : J ⥤ C} (cF₁ cF₂ : cone F) :
  Π (p : cF₁.X = cF₂.X), (Π j : J, cone.leg cF₁ j =[p; λ c, c ⟶ F.obj j] 
                                   cone.leg cF₂ j) -> cF₁ = cF₂ :=
begin 
  hinduction cF₁ with X₁ π₁, hinduction cF₂ with X₂ π₂,
  intro vertex_eq, change X₁ = X₂ at vertex_eq, hinduction vertex_eq, 
  intro legs_eq,  
  fapply apd011 cone.mk, exact idp, apply pathover_idp_of_eq,
  hinduction π₁ with app₁ nat₁, hinduction π₂ with app₂ nat₂,
  fapply apd011 nat_trans.mk, 
  { apply eq_of_homotopy, intro j, exact eq_of_pathover_idp (legs_eq j) },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott]
structure cone_map {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] {F : J ⥤ C} (cF₁ cF₂ : cone F) :=
(v_lift : cF₁.X ⟶ cF₂.X)
(fac : Π (j : J), v_lift ≫ cF₂.π.app j = cF₁.π.app j)

@[hott]
def cone_map_eq {J : Type _} [is_strict_cat J] {C : Type _} 
  [is_precat C] {F : J ⥤ C} {cF₁ cF₂ : cone F} (m₁ m₂ : cone_map cF₁ cF₂) :
  m₁.v_lift = m₂.v_lift -> m₁ = m₂ :=
begin
  hinduction m₁ with vl₁ fac₁, hinduction m₂ with vl₂ fac₂, intro v_lift_eq,
  fapply apd011, exact v_lift_eq, 
  apply pathover_of_tr_eq, apply eq_of_homotopy, intro j, exact is_prop.elim _ _
end

@[hott]
structure is_limit {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} (t : cone F) :=
(lift : Π (s : cone F), cone_map s t)
(uniq : ∀ (s : cone F) (m : cone_map s t), m.v_lift = (lift s).v_lift)

@[hott, instance]
def is_limit_is_prop {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} (t : cone F) : is_prop (is_limit t) :=
begin
  apply is_prop.mk, intros l₁ l₂, 
  hinduction l₁ with lift₁ uniq₁, hinduction l₂ with lift₂ uniq₂,
  fapply apd011,
  { apply eq_of_homotopy, intro s, apply cone_map_eq, exact uniq₂ s (lift₁ s) },
  { apply pathover_of_tr_eq, apply eq_of_homotopy2, intros s m, exact is_prop.elim _ _ }
end

@[hott] 
def lift_itself_id {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} {t : cone F} (l : is_limit t) : 
  (l.lift t).v_lift = 𝟙 t.X :=
have t_fac : ∀ j : J, 𝟙 t.X ≫ t.π.app j = t.π.app j, by intro j; hsimp,  
(l.uniq _ (cone_map.mk (𝟙 t.X) t_fac))⁻¹             

@[hott]
def limit_cone_point_iso {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} {s t : cone F} (lₛ : is_limit s) 
  (lₜ : is_limit t) : Σ i : s.X ≅ t.X, i.hom = (lₜ.lift s).v_lift :=
let st := (lₜ.lift s).v_lift, ts := (lₛ.lift t).v_lift in 
have s_fac : ∀ j : J, (st ≫ ts) ≫ s.π.app j = s.π.app j, from assume j,
  calc (st ≫ ts) ≫ s.π.app j = st ≫ (ts ≫ s.π.app j) : is_precat.assoc _ _ _
       ... = st ≫ t.π.app j : by rwr (lₛ.lift t).fac j
       ... = s.π.app j : by rwr (lₜ.lift s).fac j,
have t_fac : ∀ j : J, (ts ≫ st) ≫ t.π.app j = t.π.app j, from assume j, 
  calc (ts ≫ st) ≫ t.π.app j = ts ≫ (st ≫ t.π.app j) : is_precat.assoc _ _ _
       ... = ts ≫ s.π.app j : by rwr (lₜ.lift s).fac j 
       ... = t.π.app j : by rwr (lₛ.lift t).fac j,
have comp_s : st ≫ ts = 𝟙 s.X, from (lₛ.uniq _ (cone_map.mk _ s_fac)) ⬝ lift_itself_id lₛ, 
have comp_t : ts ≫ st = 𝟙 t.X, from (lₜ.uniq _ (cone_map.mk _ t_fac)) ⬝ lift_itself_id lₜ,
⟨iso.mk st (is_iso.mk ts comp_t comp_s), rfl⟩

/- `limit_cone F` contains a cone over `F` together with the information that 
   it is a limit. -/
@[hott]
structure limit_cone {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

@[hott]
def limit_cone_eq {J : Type _} [is_strict_cat J] 
  {C : Type u} [is_precat.{v} C] (F : J ⥤ C) (lc₁ lc₂ : limit_cone F) :
  lc₁.cone = lc₂.cone -> lc₁ = lc₂ :=
begin
  hinduction lc₁ with cone₁ is_limit₁, hinduction lc₂ with cone₂ is_limit₂,
  intro cone_eq, fapply apd011, exact cone_eq,
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

/- `has_limit F` represents the mere existence of a limit for `F`. This allows
   to define it as a class with instances. -/ 
@[hott]   
class has_limit {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] (F : J ⥤ C) :=
mk' :: (exists_limit : ∥limit_cone F∥)

@[hott]
def has_limit.mk {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} (d : limit_cone F) :=
has_limit.mk' (tr d)  

@[hott]
def has_limit_eq {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} (hlF₁ hlF₂ : has_limit F) : hlF₁ = hlF₂ :=
begin
  hinduction hlF₁ with el₁, hinduction hlF₂ with el₂,
  apply ap has_limit.mk', exact is_prop.elim _ _
end

@[hott, instance]
def has_limit_is_prop {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_precat.{v} C] {F : J ⥤ C} : is_prop (has_limit F) :=
is_prop.mk has_limit_eq

/- If `C` is a category, the limit cone vertices of two instances of 
  `limit_cone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cones and the lifts of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of limit cone points, and limit cones are equal. 
   
   Thus, we can produce a `limit_cone F` from `has_limit F`. -/
@[hott]
def limit_cone_is_unique {J : Type _} [is_strict_cat J] 
  {C : Type u} [is_cat.{v} C] (F : J ⥤ C) : 
  ∀ lc₁ lc₂ : limit_cone F, lc₁ = lc₂ :=
begin
  intros lc₁ lc₂, 
  hinduction lc₁ with cone₁ is_limit₁, hinduction lc₂ with cone₂ is_limit₂,
  let lcp_iso := limit_cone_point_iso is_limit₁ is_limit₂,
  apply limit_cone_eq, fapply cone_eq,
  { exact idtoiso⁻¹ᶠ lcp_iso.1 },
  { intro j, apply pathover_of_tr_eq,
    change idtoiso⁻¹ᶠ lcp_iso.1 ▸[λ c : C, c ⟶ F.obj j] (cone.leg cone₁ j) = _, 
    apply eq.concat (iso_hom_tr_comp lcp_iso.1 (cone.leg cone₁ j)),
    apply inverse, apply iso_move_lr, 
    have p : lcp_iso.fst.hom = (is_limit₂.lift cone₁).v_lift, from lcp_iso.2,
    rwr p, exact (is_limit₂.lift _).fac _ }
end    

@[hott, instance]
def limit_cone_is_prop {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) : is_trunc -1 (limit_cone F) :=
is_prop.mk (limit_cone_is_unique F)

@[hott]
def get_limit_cone {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) [has_limit F] : limit_cone F :=
untrunc_of_is_trunc (has_limit.exists_limit F)  

@[hott]
def limit.cone {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) [has_limit F] : cone F := 
(get_limit_cone F).cone

@[hott]
def limitcone_is_limit  {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
(get_limit_cone F).is_limit

@[hott]
def limit {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C]
  (F : J ⥤ C) [has_limit F] : C := (limit.cone F).X

@[hott]
def limit_leg {J : Type _} [is_strict_cat J] {C : Type u} 
  [is_cat.{v} C] (F : J ⥤ C) [has_limit F] (j : J) : 
  limit F ⟶ F.obj j := (limit.cone F).π.app j 

@[hott]
def diag_eq_lim_eq_lim {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C]
  {F F' : J ⥤ C} (p : F = F') [hlF : has_limit F] [hlF' : has_limit F'] : 
  @limit _ _ _ _ F hlF = @limit _ _ _ _ F' hlF' :=
apd011 (@limit _ _ _ _) p (pathover_of_tr_eq (has_limit_eq _ _))  

@[hott]
def diag_inv_eq_lim_eq {J : Type _} [is_strict_cat J] {C : Type u} [is_cat.{v} C]
  {F F' : J ⥤ C} (p : F = F') [hlF : has_limit F] [hlF' : has_limit F'] :
  (diag_eq_lim_eq_lim p⁻¹) = (diag_eq_lim_eq_lim p)⁻¹ :=
begin
  change apd011 _ _ _ = eq.inverse (apd011 _ _ _), 
  rwr apd011_inv, apply ap (apd011 limit p⁻¹), rwr pathover_of_tr_eq_inv, 
  apply ap pathover_of_tr_eq, exact is_prop.elim _ _ 
end

@[hott]
def diag_eq_leg_eq {J : Type _} [is_strict_cat J] {C : Type _} [is_cat C]
  {F F' : J ⥤ C} (p : F = F') (j : J) [hlF : has_limit F] [hlF' : has_limit F'] :
  limit_leg F' j = ((ap (λ F : J ⥤ C, F.obj j) p) ▸[λ d : C, limit F' ⟶ d] 
                   ((diag_eq_lim_eq_lim p) ▸[λ c : C, c ⟶ F.obj j] limit_leg F j)) :=
@tr_tr_fn2_fn2_fn _ C C _ _ p _ _ _ (pathover_of_tr_eq (has_limit_eq (p ▸ hlF) hlF'))
                 (λ d e : C, d ⟶ e) _ _ (λ (F : J ⥤ C) (hlF : has_limit F), 
                                                          @limit_leg _ _ _ _ F hlF j)

/- Limits of diagrams of shapes with a functor between them are not necessarily naturally
   mapped to each other. But limits of diagrams of isomorphic shapes are naturally 
   isomorphic and hence equal. -/
@[hott]
def cone_to_diag_iso_cone {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} (s : cone F) : cone (H.hom ⋙ F) :=
begin
  fapply cone.mk, exact s.X, fapply nat_trans.mk, 
  { intro j₁, exact s.π.app (H.hom.obj j₁) },
  { intros j₁ j₁' f, exact s.π.naturality _ }
end 

@[hott]
def cone_to_diag_iso_cone_inv {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} (t : cone (H.hom ⋙ F)) : cone F :=
begin
  fapply cone.mk, exact t.X, fapply nat_trans.mk, 
  { intro j₂, exact t.π.app (H.ih.inv.obj j₂) ≫ F.map ((functor_eq_to_nat_trans H.ih.r_inv).app j₂) },
  { intros j₂ j₂' f, change (constant_functor t.X).map (H.ih.inv.map f) ≫ _ = _,
    rwr <- is_precat.assoc ((constant_functor t.X).map f), rwr t.π.naturality (H.ih.inv.map f), 
    rwr is_precat.assoc, change _ ≫ F.map _ ≫ _ = _, rwr <- F.map_comp, rwr is_precat.assoc, rwr <- F.map_comp,
    change _ = _ ≫ F.map (_ ≫ ((𝟙 J₂ : J₂.obj ⥤ J₂.obj).map f)), 
    rwr <- (functor_eq_to_nat_trans H.ih.r_inv).naturality f }
end 

@[hott]
def cone_to_diag_iso_cone_map {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} (cF : cone F) (cHF : cone (H.hom ⋙ F)) : 
  cone_map ((cone_to_diag_iso_cone_inv H cHF)) cF -> cone_map cHF (cone_to_diag_iso_cone H cF) :=
begin 
  intro m, fapply cone_map.mk,
  { exact m.v_lift },
  { intro j₁, change _ ≫ cF.π.app (H.hom.obj j₁) = _, rwr m.fac (H.hom.obj j₁), 
    change cHF.π.app _ ≫ F.map _ = _, 
    have p : F.map ((functor_eq_to_nat_trans H.ih.r_inv).app (H.hom.obj j₁)) = 
             (H.hom ⋙ F).map ((functor_eq_to_nat_trans H.ih.l_inv).app j₁), from 
    begin 
      change F.map _ = F.map _, apply ap (@precategories.functor.map _ _ _ _ F _ _), 
      change (idtoiso _).hom = H.hom.map (idtoiso _).hom, rwr funct_idtoiso, 
      apply ap (λ p, (idtoiso p).hom), exact is_prop.elim _ _ 
    end,
    rwr p, rwr <- cHF.π.naturality, change 𝟙 _ ≫ _ = _, rwr is_precat.id_comp }
end

@[hott]
def cone_to_diag_iso_cone_map_inv {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} (cF : cone F) (cHF : cone (H.hom ⋙ F)) : 
  cone_map cHF (cone_to_diag_iso_cone H cF) -> cone_map ((cone_to_diag_iso_cone_inv H cHF)) cF :=
begin 
  intro m, fapply cone_map.mk,
  { exact m.v_lift },
  { intro j₂, change _ = cHF.π.app _ ≫ _, rwr <- m.fac (H.ih.inv.obj j₂), rwr is_precat.assoc, 
    change _ = _ ≫ cF.π.app _ ≫ _, rwr <- cF.π.naturality, change _ = _ ≫ 𝟙 _ ≫ _, 
    rwr is_precat.id_comp }
end

@[hott]
def cone_to_diag_iso_cone_map_vert {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} {cF : cone F} {cHF : cone (H.hom ⋙ F)} 
  (m : cone_map ((cone_to_diag_iso_cone_inv H cHF)) cF) : 
  m.v_lift = (cone_to_diag_iso_cone_map H cF cHF m).v_lift := idp

@[hott]
def cone_to_diag_iso_cone_map_vert_inv {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C] (H : J₁ ≅ J₂) 
  {F : J₂.obj ⥤ C} {cF : cone F} {cHF : cone (H.hom ⋙ F)} (m : cone_map cHF ((cone_to_diag_iso_cone H cF))) : 
  m.v_lift = (cone_to_diag_iso_cone_map_inv H cF cHF m).v_lift := idp

@[hott]
def diag_id_iso_cone {J : Strict_Categories} {C : Type u} [is_cat.{v} C] {F : J.obj ⥤ C} (cF : cone F) : 
  cone_to_diag_iso_cone (id_iso J) cF = cone.mk cF.X (nat_trans.mk cF.π.app cF.π.naturality) := idp

@[hott]
def diag_iso_cone_vertex {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} (cF : cone F) : 
  (cone_to_diag_iso_cone H cF).X = cF.X :=
idp 

@[hott]
def diag_iso_cone_legs {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} (cF : cone F) : Π (j₁ : J₁.obj),
  (cone.leg (cone_to_diag_iso_cone H cF) j₁) = 
  ((diag_iso_cone_vertex H cF)⁻¹ ▸[λ c : C, c ⟶ F.obj (H.hom.obj j₁)] cone.leg cF (H.hom.obj j₁)) :=
begin intro j₁, exact idp end

@[hott]
def diag_iso_cone_legs_fac {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} (cF : cone F) : Π (j₁ : J₁.obj), 
  ((idtoiso (diag_iso_cone_vertex H cF)).hom ≫ cone.leg cF (H.hom.obj j₁)) = 
                                      cone.leg (cone_to_diag_iso_cone H cF) j₁ :=
begin intro j₁, rwr diag_iso_cone_legs, rwr id_hom_tr_comp end

@[hott]
def diag_iso_cone_is_lim {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} {cF : cone F} (lcF : is_limit cF) : 
  is_limit (cone_to_diag_iso_cone H cF) :=
begin
  fapply is_limit.mk, 
  { intro s, apply cone_to_diag_iso_cone_map, apply lcF.lift },
  { intros s m, rwr <- cone_to_diag_iso_cone_map_vert, rwr cone_to_diag_iso_cone_map_vert_inv,
    apply lcF.uniq }
end

@[hott, instance]
def diag_iso_has_lim_to_has_lim {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) {F : J₂.obj ⥤ C} [hlF : has_limit F] : has_limit (H.hom ⋙ F) :=
begin 
  apply has_limit.mk, fapply limit_cone.mk, 
  exact cone_to_diag_iso_cone H (limit.cone F),
  exact diag_iso_cone_is_lim H (limitcone_is_limit _)
end

@[hott]
def diag_iso_lim_eq_lim {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) (F : J₂.obj ⥤ C) [hlF : has_limit F] : 
  @limit _ _ _ _ (H.hom ⋙ F) (diag_iso_has_lim_to_has_lim H) = limit F  :=
begin exact (diag_iso_cone_vertex H (limit.cone F)) end

@[hott]
def diag_iso_lim_legs_eq {J₁ J₂ : Strict_Categories} {C : Type u} [is_cat.{v} C]
  (H : J₁ ≅ J₂) (F : J₂.obj ⥤ C) [hlF : has_limit F] :
  Π (j₁ : J₁.obj), (idtoiso (diag_iso_lim_eq_lim H F)).hom ≫ limit_leg F (H.hom.obj j₁) =
                limit_leg (H.hom ⋙ F) j₁ :=
assume j₁, diag_iso_cone_legs_fac H (limit.cone F) j₁


/- More general classes of existence of limits -/
@[hott]
class has_limits_of_shape (J : Type _) [is_strict_cat J] 
  (C : Type u) [is_cat.{v} C] :=
(has_limit : Π F : J ⥤ C, has_limit F)

@[hott, instance]
def has_lims_shape_is_prop (J : Type _) [is_strict_cat J] (C : Type u) [is_cat.{v} C] : 
  is_prop (has_limits_of_shape J C) :=
begin 
  apply is_prop.mk, intros hls₁ hls₂, hinduction hls₁, hinduction hls₂,
  apply ap has_limits_of_shape.mk, exact is_prop.elim _ _ 
end

@[hott, priority 100]
instance has_limit_of_has_limits_of_shape
  {J : Type _} [is_strict_cat J] (C : Type u) [is_cat.{v} C] 
  [has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[hott]
class has_limits (C : Type u) [is_cat.{v} C] :=
  (has_limit_of_shape : Π {J : Type _} [is_strict_cat J], 
                                       has_limits_of_shape J C )  

@[hott]
class has_product {C : Type u} [is_cat.{v} C] {J : Set.{u'}} 
  (f : J -> C) := (has_limit : has_limit (discrete.functor f)) 

@[hott, priority 100]
instance has_limit_of_has_product {C : Type u} [is_cat.{v} C] 
  {J : Set.{u'}} (f : J -> C) [has_product f] : has_limit (discrete.functor f) := 
has_product.has_limit f  

@[hott]
abbreviation pi_obj {C : Type u} [is_cat.{v} C] {J : Set.{u'}} (f : J → C) 
  [has_product f] := limit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f

@[hott]
class has_products (C : Type u) [is_cat.{v} C] := 
  (has_limit_of_shape : Π J : Set.{u'}, has_limits_of_shape (discrete J) C)

@[hott, instance, priority 100]
def has_limits_of_shape_of_has_products 
  (J : Set.{u'}) (C : Type u) [is_cat.{v} C] [has_products.{v u u'} C] :
  has_limits_of_shape (discrete J) C :=
has_products.has_limit_of_shape C J

@[hott]
instance has_product_of_has_products {C : Type u} [is_cat.{v} C] 
  [has_products C] {J : Set.{u'}} (f : J -> C) : has_product f :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_products.has_limit_of_shape C J) (discrete.functor f)⟩

@[hott, instance]
def has_product_of_has_limits_of_shape {C : Type u} [is_cat.{v} C] 
  {J : Set.{u'}} [has_limits_of_shape (discrete J) C] (f : J -> C) : 
  has_product f :=
⟨has_limits_of_shape.has_limit (discrete.functor f)⟩ 

@[hott, instance]
def has_products_of_has_limits (C : Type u) [is_cat.{v} C] [c : has_limits C] : 
  has_products C :=
has_products.mk (λ J, @has_limits.has_limit_of_shape C _ c (discrete J) _)

/-- A fan over `f : J → C` consists of a collection of maps from an object `P`
    to every `f j`. This is enough to determine a cone which factorizes through    
    the product. -/
@[hott]    
abbreviation fan {J : Set.{u'}} {C : Type u} [is_cat.{v} C] (f : J → C) := 
  cone (discrete.functor f)

@[hott, hsimp]
def fan.mk {J : Set.{u'}} (C : Type u) [is_cat.{v} C] {f : J → C} {P : C} 
  (p : Π j, P ⟶ f j) : fan f :=
cone.mk P (discrete.nat_trans p)

@[hott, hsimp] 
def pi.lift {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} [has_product f]
  {P : C} (p : Π j, P ⟶ f j) : P ⟶ ∏ f :=
((get_limit_cone (discrete.functor f)).is_limit.lift (fan.mk _ p)).v_lift  

@[hott, hsimp] 
def pi.π {J : Set.{u'}} {C : Type u} [is_cat.{v} C] (f : J → C) [has_product f] 
  (j : J) : ∏ f ⟶ f j :=
(limit.cone (discrete.functor f)).π.app j 

@[hott]
def pi.hom_is_lift {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} 
  [has_product f] {P : C} (h : P ⟶ ∏ f) : 
  h = pi.lift (λ j : J, h ≫ (pi.π _ j)) :=
let p := λ j : J, h ≫ (pi.π f j),
    c := fan.mk _ p,
    lc := get_limit_cone (discrete.functor f) in     
begin 
  change h = (lc.is_limit.lift c).v_lift, 
  apply is_limit.uniq lc.is_limit c (cone_map.mk h (λ j, rfl))
end  

@[hott]
def pi.lift_π_eq {J : Set.{u'}} (C : Type u) [is_cat.{v} C] {f : J → C} 
  [has_product f] {P : C} (p : Π j : J, P ⟶ f j) : 
  ∀ j : J, pi.lift p ≫ pi.π _ j = p j :=
((get_limit_cone (discrete.functor f)).is_limit.lift (fan.mk _ p)).fac  

@[hott]
def pi.lift_uniq {J : Set.{u'}} (C : Type u) [is_cat.{v} C] {f : J → C} 
  [has_product f] {P : C} {p : Π j : J, P ⟶ f j} :=
((get_limit_cone (discrete.functor f)).is_limit.lift (fan.mk _ p)).fac   

@[hott]
def pi.lift_fac {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f : J → C} 
  [has_product f] {P Q : C} (g : Q ⟶ P) (h : Π j : J, P ⟶ f j) :
  pi.lift (λ j, g ≫ h j) = g ≫ pi.lift h :=
let ch := fan.mk _ h, p := λ j : J, g ≫ h j, cp := fan.mk _ p, 
    lc := get_limit_cone (discrete.functor f) in  
begin
  have p_fac : Π j : J, (g ≫ pi.lift h) ≫ pi.π _ j = g ≫ h j, from 
    begin intro j, rwr is_precat.assoc, rwr pi.lift_π_eq end,  
  exact (is_limit.uniq lc.is_limit cp (cone_map.mk (g ≫ pi.lift h) p_fac))⁻¹
end  

@[hott]
def pi_hom {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f g : J -> C} 
  [has_product f] [has_product g] (h : Π j : J, f j ⟶ g j) : ∏ f ⟶ ∏ g :=
pi.lift (λ j : J, pi.π f j ≫ h j)

notation `∏h ` h:20 := pi_hom h

@[hott]
def pi_hom_id {J : Set.{u'}} {C : Type u} [is_cat.{v} C] (f : J -> C) [has_product f] : 
  pi_hom (λ j, 𝟙 (f j)) = 𝟙 (∏ f) :=
have H : (λ j, pi.π f j ≫ 𝟙 (f j)) = λ j, 𝟙 (∏ f) ≫ pi.π f j, from 
  begin apply eq_of_homotopy, intro j, hsimp end,  
begin change pi.lift (λ j, pi.π f j ≫ 𝟙 (f j)) = _, rwr H, rwr <- pi.hom_is_lift end  

@[hott]
def pi_hom_comp {J : Set.{u'}} {C : Type u} [is_cat.{v} C] {f g h : J -> C} 
  [has_product f] [has_product g] [has_product h] (i₁ : Π j : J, f j ⟶ g j)  
  (i₂ : Π j : J, g j ⟶ h j) : (∏h i₁) ≫ (∏h i₂) = ∏h (λ j, i₁ j ≫ i₂ j) :=
have H : (λ j, pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j) = 
                                             λ j, pi.π f j ≫ i₁ j ≫ i₂ j, from   
  begin 
    apply eq_of_homotopy, intro j, 
    change pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j = _,
    rwr <- is_precat.assoc, rwr pi.lift_π_eq, 
    change (pi.π f j ≫ i₁ j) ≫ i₂ j = pi.π f j ≫ i₁ j ≫ i₂ j, rwr is_precat.assoc 
  end,
calc pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.lift (λ j, pi.π g j ≫ i₂ j) = 
           pi.lift (λ j, pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j) : 
                                                          by rwr <- pi.lift_fac
     ... = pi.lift (λ j, pi.π f j ≫ i₁ j ≫ i₂ j) : by rwr H

@[hott]
def pi_proj_sset {J : Set.{u'}} {A B : Subset J} (inc : A ⊆ B) {C : Type u} 
  [is_cat.{v} C] (f : pred_Set B -> C) [has_product f] 
  [has_product (f ∘ pred_Set_inc inc)] : ∏ f ⟶ ∏ (f ∘ pred_Set_inc inc) :=
pi.lift (λ j : pred_Set A, pi.π f (pred_Set_inc inc j))


/- The full subcategory on a subtype of a category with limits has limits if the limit
   of a diagram of objects of the subtype is also in the subtype. -/
@[hott]
def limit_closed_subtype {J : Type _} [H : is_strict_cat J] {C : Type u} [is_cat.{v} C]   
  (P : C -> trunctype.{0} -1) (F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))) :=
∀ (lc : limit_cone (embed F)), (P lc.cone.X).carrier

@[hott] 
def emb_cone {J : Type _} [H : is_strict_cat J] {C : Type u} [is_cat.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  (s : cone F) : cone (embed F) :=
begin
  fapply cone.mk, 
  { exact s.X.1 },
  { fapply nat_trans.mk,
    { intro j, exact s.π.app j },
    { intros j k f, exact s.π.naturality f } }
end  

@[hott]
def subcat_limit_cone {J : Type _} [H : is_strict_cat J] {C : Type u} [is_cat.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  (lc : limit_cone (embed F)) (lim_clos : (P lc.cone.X).carrier) : 
  limit_cone F :=
begin
  fapply limit_cone.mk,
  { fapply cone.mk,
    { exact ⟨lc.cone.X, lim_clos⟩ },
    { fapply nat_trans.mk, 
      { intro j, exact lc.cone.π.app j },
      { intros j k f, exact lc.cone.π.naturality f } } },
  { fapply is_limit.mk,
    { intro s, fapply cone_map.mk,
      { exact (lc.is_limit.lift (emb_cone s)).v_lift },
      { intro j, exact (lc.is_limit.lift (emb_cone s)).fac j } },
    { intros s m, 
      exact lc.is_limit.uniq (emb_cone s) (cone_map.mk m.v_lift (λ j, m.fac j)) } }
end  

@[hott, instance]
def subcat_has_limit {J : Type _} [H : is_strict_cat J] {C : Type u} [is_cat.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  [has_limit (embed F)] (lim_clos : limit_closed_subtype P F) : has_limit F :=
has_limit.mk (subcat_limit_cone (get_limit_cone (embed F)) 
             (lim_clos (get_limit_cone (embed F))))

@[hott, instance]
def subcat_has_limits_of_shape {J : Type _} [H : is_strict_cat J] {C : Type u} [is_cat.{v} C]   
  {P : C -> trunctype.{0} -1} [has_limits_of_shape J C] 
  (lim_clos : ∀ F : J ⥤ (sigma.subtype (λ c : C, ↥(P c))), 
                                                  @limit_closed_subtype J _ _ _ P F) : 
  has_limits_of_shape J (sigma.subtype (λ c : C, ↥(P c))) :=
has_limits_of_shape.mk (λ F, subcat_has_limit (lim_clos F))     

@[hott, instance]
def subcat_has_products {C : Type u} [is_cat.{v} C] {P : C -> trunctype.{0} -1} 
  [has_products C] 
  (lim_clos : ∀ (J : Set) (F : (discrete J) ⥤ (sigma.subtype (λ c : C, ↥(P c)))), 
                                  limit_closed_subtype P F) : 
  has_products (sigma.subtype (λ c : C, ↥(P c))) :=
⟨λ J : Set, @subcat_has_limits_of_shape (discrete J) _ _ _ _ 
             (has_limits_of_shape_of_has_products J C) (lim_clos J)⟩

/- We introduce the terminal object in a category together with some of its properties; 
  it exists if the category has limits. -/
@[hott]
class terminal (C : Type u) [is_cat.{v} C] := 
  (term_obj : C)
  (term_map : Π (c : C), c ⟶ term_obj)
  (uniq : Π {c : C} (f g : c ⟶ term_obj), f = g)

@[hott, instance]
def terminal_of_has_product (C : Type u) [is_cat.{v} C] 
  [H : has_product (empty_map.{u u} C)] : terminal C :=
begin
  fapply terminal.mk,
  { exact @pi_obj _ _ _ (empty_map C) H },
  { intro c, apply pi.lift, intro j, hinduction j },
  { intros c f g, 
    let cc := @fan.mk _ C _ (empty_map.{u u} C) c (λ j : false, false.rec _ j),
    let mcf : cone_map cc (get_limit_cone (discrete.functor (empty_map C))).cone := 
      begin fapply cone_map.mk, exact f, exact (λ j : false, false.rec _ j) end,
    let mcg : cone_map cc (get_limit_cone (discrete.functor (empty_map C))).cone := 
      begin fapply cone_map.mk, exact g, exact (λ j : false, false.rec _ j) end,
    change mcf.v_lift = mcg.v_lift, 
    let p := (get_limit_cone (discrete.functor (empty_map.{u u} C))).is_limit.uniq, 
    rwr p cc mcf, rwr p cc mcg }
end

@[hott]
def terminal_map_is_mono (C : Type u) [is_cat.{v} C] [H : terminal C] {c : C} :
  Π (f : H.term_obj ⟶ c), is_mono f :=
begin intros f d g₁ g₂ p, apply H.uniq end

@[hott]
def term_subobj (C : Type u) [is_cat.{v} C] [H : terminal C] {c : C} (f : H.term_obj ⟶ c) :
  subobject c := (subobject.mk H.term_obj f (terminal_map_is_mono C f))

end categories.limits

end hott