import hott.algebra.ring set_theory categories.examples categories.cat_limits pathover2
       hott.types.prod rings.basic

universes v v' u u' w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set subset categories hott.trunc
     hott.category_theory.limits hott.sigma hott.prod 

namespace algebra

/-  The category `CommRing` has all limits. 

   To prove this we use the criterion in [cat_limits], for which we need to show the following:
   - Products of the underlying sets of commutative rings are also commutative rings.
   - using the subring criterion above we show that the vertices of limit cones of the underlying 
     sets of commutative rings are commutative rings. 
   - The legs and lifts are ring homomorphisms because the subring embedding is a ring 
     homomorphism and the projections from and the lift to product rings are ring homomorphisms. -/
@[hott, reducible]
def CommRing_product_str {J : Set.{u}} (F : J -> CommRing.{u}) : 
  comm_ring (Sections (λ j : J, (F j).carrier)) :=
begin  
  fapply comm_ring_mk,
  { fapply comm_ring_ops.mk, 
    { intros r s, exact λ j, (r j) + (s j) }, --add 
    { exact λ j, 0 }, --zero 
    { intro r, exact λ j, -(r j) }, --neg 
    { intros r s, exact λ j, (r j) * (s j) }, --mul
    { exact λ j,  1 } }, --one
  { fapply comm_ring_laws.mk, 
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_assoc _ _ _ },
                                                                                         --add_assoc
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.zero_add _ }, --zero_add 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_zero _ }, --add_zero 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_left_inv _ }, 
                                                                                     --add_left_inv
    { intros r s, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_comm _ _ }, 
                                                                                     --add_comm 
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_assoc _ _ _ },
                                                                                       --mul_assoc 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.one_mul _ }, --one_mul 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_one _ }, --mul_one 
    { intros r s, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_comm _ _ }, 
                                                                                         --mul_comm
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.left_distrib _ _ _ }, 
                                                                                      --left_distrib
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.right_distrib _ _ _ } } 
                                                                                    --right_distrib
end    

@[hott]
def CommRing_product {J : Set.{u}} (F : J -> CommRing.{u}) : CommRing :=
  CommRing.mk (Sections.{u u} (λ j : J, (F j).carrier)) (CommRing_product_str F)

@[hott]
def CommRing_product_proj_hom {J : Set.{u}} (F : J -> CommRing.{u}) : 
  ∀ j : J, comm_ring_str.H (CommRing_product_str F) (F j).str (λ s, s j) :=
begin  
  intro j, fapply is_ring_hom.mk, 
  { refl }, 
  { intros r s, refl }, 
  { refl }, 
  { intros r s, refl },  
end

@[hott]
def ring_limit_pred {J : Set.{u}} [precategory.{u} J] (F : J ⥤ CommRing.{u}) : 
  Setpred (CommRing_product F.obj).carrier :=
set_limit_pred (forget.{u u u+1 u} F)  

@[hott, instance]
def ring_pred_is_closed {J : Set.{u}} [precategory.{u} J] (F : J ⥤ CommRing.{u}) :
  ring_pred_closed (ring_limit_pred F) :=
begin
  fapply ring_pred_closed.mk, 
  { intros r s Hr Hs j k f, change (F.map f).1 (r j + s j) = (r k + s k : F.obj k),
    rwr (F.map f).2.map_add (r j) (s j), 
    have pr : (F.map f).1 (r j) = r k, from Hr j k f, 
    have ps : (F.map f).1 (s j) = s k, from Hs j k f,
    rwr pr, rwr ps }, --closed_add
  { intros j k f, change (F.map f).1 0 = (0 : F.obj k), rwr (F.map f).2.map_zero }, 
      --closed_zero
  { intros r Hr j k f, change (F.map f).1 (-(r j)) = (-(r k) : F.obj k),
    rwr comm_ring_hom.map_neg (F.map f).2 (r j), 
    have pr : (F.map f).1 (r j) = r k, from Hr j k f, rwr pr }, --closed_neg
  { intros r s Hr Hs j k f, change (F.map f).1 (r j * s j) = (r k * s k : F.obj k),
    rwr (F.map f).2.map_mul (r j) (s j), 
    have pr : (F.map f).1 (r j) = r k, from Hr j k f, 
    have ps : (F.map f).1 (s j) = s k, from Hs j k f,
    rwr pr, rwr ps }, --closed_mul
  { intros j k f, change (F.map f).1 1 = (1 : F.obj k), rwr (F.map f).2.map_one }, 
      --closed_one
    end  

@[hott]
def limit_comm_ring {J : Set.{u}} [precategory.{u} J] (F : J ⥤ CommRing.{u}) :
  comm_ring_str.P (set_limit_cone (forget F)).cone.X :=
begin    
  exact @comm_subring.{u u} (CommRing_product F.obj) (ring_limit_pred F) (ring_pred_is_closed F)
end    

@[hott]
def CommRing_limit_cone {J : Set.{u}} [precategory.{u} J] (F : J ⥤ CommRing.{u}) : 
  limit_cone F :=
begin 
  fapply str_limit_cone (set_limit_cone (forget F)), 
  fapply limit_cone_str_data.mk,
  { exact limit_comm_ring F }, --lc_str
  { intro j, 
    change ↥(comm_ring_str.H (limit_comm_ring F) (F.obj j).str 
             ((CommSubring.to_Subset (ring_limit_pred F)).map ≫ (λ u, u j))), 
    fapply comm_ring_str.comp_H _ (CommRing_product F.obj).str, 
    { exact comm_subring_embed_hom (ring_limit_pred F) },
    { exact CommRing_product_proj_hom F.obj j } }, --lc_legs_H
  { intro s, fapply is_ring_hom.mk, 
    { fapply sigma_eq,
      { change (λ j, (s.π.app j).1 (1 : s.X.carrier)) = (λ j, (1 : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_one }, 
      { apply pathover_of_tr_eq, apply is_prop.elim } },
    { intros t₁ t₂, fapply sigma_eq, 
      { change (λ j, (s.π.app j).1 (t₁ * t₂)) = 
                              (λ j, (((s.π.app j).1 t₁) * ((s.π.app j).1 t₂) : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_mul t₁ t₂ },
      { apply pathover_of_tr_eq, apply is_prop.elim } },  
    { fapply sigma_eq,
      { change (λ j, (s.π.app j).1 (0 : s.X.carrier)) = (λ j, (0 : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_zero }, 
      { apply pathover_of_tr_eq, apply is_prop.elim } },    
    { intros t₁ t₂, fapply sigma_eq, 
      { change (λ j, (s.π.app j).1 (t₁ + t₂)) = 
                              (λ j, (((s.π.app j).1 t₁) + ((s.π.app j).1 t₂) : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_add t₁ t₂ },
      { apply pathover_of_tr_eq, apply is_prop.elim } } } --lift_H
end   

@[hott]
def CommRing_has_limit {J : Set.{u}} [precategory.{u} J] (F : J ⥤ CommRing.{u}) : 
  has_limit F :=
has_limit.mk (CommRing_limit_cone F)

@[hott, instance]
def CommRing_has_limits_of_shape (J : Set.{u}) [precategory.{u} J] :
  has_limits_of_shape J CommRing.{u} :=
has_limits_of_shape.mk (λ F, CommRing_has_limit F) 

@[hott, instance]
def CommRing_has_limits : has_limits CommRing.{u} :=
  has_limits.mk (λ (J : Set.{u}) (c : precategory.{u} J), @CommRing_has_limits_of_shape J c)

@[hott, instance]
def CommRing_has_products : has_products CommRing :=
begin
  exact @has_products_of_has_limits CommRing _ CommRing_has_limits
end

end algebra

end hott