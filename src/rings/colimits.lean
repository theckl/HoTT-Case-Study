import hott.algebra.ring sets.basic categories.examples init2
       hott.types.prod hott.algebra.relation categories.cat_colimits rings.basic 

universes v v' u u' w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set subset categories hott.trunc
     hott.sigma hott.prod hott.relation hott.category_theory.colimits

namespace algebra

/- We now show that the category of commutative rings has all colimits. 
   
   To construct colimits of diagrams of rings we follow the strategy in 
   [mathlib.algebra.category.CommRing.colimits] and define as a quotient of the expressions
   freely generated by the ring operations applied on the elements of the rings in the 
   diagram, modulo the ring relations and the compatibility relations induced by the diagram.

   At this moment, we do not split this up into the construction of the free commutative 
   ring associated to a set, as the left adjoint functor to the forgetful functor, and then
   the quotient by the compatibility relations - it adds an additional layer to calculations
   and proofs, without shortening the construction. -/
@[hott]
inductive expr {J : Set.{u'}} [precategory.{v'} J] (F : J ⥤ CommRing.{u}) : Type (max u' v' u)
-- one free variable $x_{j,r}$ for each element r in each ring of the diagram
| x_ : Π (j : J) (r : F.obj j), expr
-- Then one generator for each operation
| zero : expr
| one : expr
| neg : expr → expr
| add : expr → expr → expr
| mul : expr → expr → expr

/- The inductive type `expr` is a set. We show this by the encode-decode method, which
  requires a lot of case distinction. There should be potential for automatisation; the
  `injection` tactic may provide short-cuts. -/
@[hott, reducible]
def code_expr {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  expr F -> expr F -> Type _  
| (expr.x_ j r) (expr.x_ k s) := Σ (p : j = k), (r =[p; λ i : J, F.obj i] s)
| (expr.zero _) (expr.zero _) := One
| (expr.one _) (expr.one _) := One
| (expr.neg x) (expr.neg y) := code_expr x y
| (expr.add x₁ x₂) (expr.add y₁ y₂) := prod (code_expr x₁ y₁) (code_expr x₂ y₂)
| (expr.mul x₁ x₂) (expr.mul y₁ y₂) := prod (code_expr x₁ y₁) (code_expr x₂ y₂)
| _ _ := Zero 

@[hott, reducible]
def code_expr.rec {J : Set} [precategory J] (F : J ⥤ CommRing) 
  {P : Type _ -> Type _} (H1 : Π j k r s, P (code_expr F (expr.x_ j r) (expr.x_ k s))) 
  (H2 : P One) (H3 : P Zero) 
  (H4 : Π {x y}, P (code_expr F x y) -> P (code_expr F (expr.neg x) (expr.neg y)))
  (H5 : Π {x₁ x₂ y₁ y₂}, P (code_expr F x₁ y₁) -> P (code_expr F x₂ y₂) ->
                       P (code_expr F (expr.add x₁ x₂) (expr.add y₁ y₂))) 
  (H6 : Π {x₁ x₂ y₁ y₂}, P (code_expr F x₁ y₁) -> P (code_expr F x₂ y₂) ->
                       P (code_expr F (expr.mul x₁ x₂) (expr.mul y₁ y₂))) :                    
  Π (x y : expr F), P (code_expr F x y) :=         
begin 
  intro x; hinduction x; intro y; hinduction y, any_goals { assumption }, 
  { exact H1 j j_1 r r_1 },
  { exact H4 (ih a_1) }, 
  { exact H5 (ih_a a_2) (ih_a_1 a_3) },
  { exact H6 (ih_a a_2) (ih_a_1 a_3) }
end  

@[hott, reducible]
def code_fun {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  Π (x : expr F), code_expr F x x :=
begin 
  fapply expr.rec, 
  { intros j r, exact ⟨idp, idpo⟩ },
  { exact One.star },
  { exact One.star },
  { intros x cx, exact cx },
  { intros x y cx cy, exact ⟨cx, cy⟩ },
  { intros x y cx cy, exact ⟨cx, cy⟩ }
end  

@[hott, reducible]
def encode_expr {J : Set} [precategory J] (F : J ⥤ CommRing) :
  Π (x y : expr F), (x = y) -> code_expr F x y :=
assume x y p, p ▸ (code_fun F x)

@[hott, reducible]
def decode_expr {J : Set} [precategory J] (F : J ⥤ CommRing) :
  Π (x y : expr F), (code_expr F x y) -> x = y :=
begin
  intro x, hinduction x; intro y; hinduction y; intro c,
  any_goals { exact Zero.rec _ c}, 
  { exact apd011 expr.x_ c.1 c.2 },
  { exact idp },
  { exact idp },
  { exact ap expr.neg (ih a_1 c) },
  { exact ap011 expr.add (ih_a a_2 c.1) (ih_a_1 a_3 c.2) },
  { exact ap011 expr.mul (ih_a a_2 c.1) (ih_a_1 a_3 c.2) }
end    

@[hott, reducible]
def expr_eq_equiv_code {J : Set} [precategory J] (F : J ⥤ CommRing) :
  Π (x y : expr F), (x = y) ≃ (code_expr F x y) := 
have rinv : Π (x y : expr F) (c : code_expr F x y), 
              encode_expr F x y (decode_expr F x y c) = c, from
  begin 
    intro x, hinduction x; intro y; hinduction y; intro c,
    any_goals { exact Zero.rec _ c}, 
    { hinduction c with c1 c2, hinduction c1, hinduction c2, refl },
    { hinduction c, refl },
    { hinduction c, refl },
    { change ap expr.neg (decode_expr F a a_1 c) ▸[λ y : expr F, 
                             code_expr F (expr.neg a) y] (code_fun F (expr.neg a)) = c, 
      rwr <- tr_compose, change decode_expr F a a_1 c ▸ code_fun F a = c, exact ih a_1 c },
    { hinduction c with c₁ c₂, 
      change ap011 expr.add (decode_expr _ _ _ c₁) (decode_expr _ _ _ c₂) ▸[λ y : expr F, 
                  code_expr F (expr.add a a_1) y] (code_fun F (expr.add a a_1)) = (c₁, c₂),
      rwr @tr_ap011 _ _ _ _ _ _ _ (λ x y : expr F, code_expr F x y) expr.add 
          (code_fun F) (decode_expr F a a_2 c₁) (decode_expr F a_1 a_3 c₂), 
      have p : code_fun F (expr.add a a_1) = (code_fun F a, code_fun F a_1), from rfl,      
      rwr p, 
      rwr @tr_tr_pair _ _ (λ x y : expr F, code_expr F x y) (code_fun F) 
                          (λ x y : expr F, code_expr F x y) (code_fun F) _ _ _ _ 
                          (decode_expr F a a_2 c₁) (decode_expr F a_1 a_3 c₂), 
      apply pair_eq, exact ih_a a_2 c₁, exact ih_a_1 a_3 c₂ },
    { hinduction c with c₁ c₂, 
      change ap011 expr.mul (decode_expr _ _ _ c₁) (decode_expr _ _ _ c₂) ▸[λ y : expr F, 
                  code_expr F (expr.mul a a_1) y] (code_fun F (expr.mul a a_1)) = (c₁, c₂),
      rwr @tr_ap011 _ _ _ _ _ _ _ (λ x y : expr F, code_expr F x y) expr.mul 
          (code_fun F) (decode_expr F a a_2 c₁) (decode_expr F a_1 a_3 c₂), 
      have p : code_fun F (expr.mul a a_1) = (code_fun F a, code_fun F a_1), from rfl,      
      rwr p, 
      rwr @tr_tr_pair _ _ (λ x y : expr F, code_expr F x y) (code_fun F) 
                          (λ x y : expr F, code_expr F x y) (code_fun F) _ _ _ _ 
                          (decode_expr F a a_2 c₁) (decode_expr F a_1 a_3 c₂), 
      apply pair_eq, exact ih_a a_2 c₁, exact ih_a_1 a_3 c₂ } 
  end,
have linv : Π (x y : expr F) (p : x = y), decode_expr F x y (encode_expr F x y p) = p, from 
  begin 
    intros x y p, hinduction p, change decode_expr F x x (code_fun F x) = refl x, 
    hinduction x,
    { refl }, { refl }, { refl },
    { change ap expr.neg (decode_expr F a a (code_fun F a)) = refl (expr.neg a), rwr ih },
    { change ap011 expr.add (decode_expr F a a (code_fun F a)) 
                            (decode_expr F a_1 a_1 (code_fun F a_1)) = refl (expr.add a a_1),
      rwr ih_a, rwr ih_a_1 },
    { change ap011 expr.mul (decode_expr F a a (code_fun F a)) 
                            (decode_expr F a_1 a_1 (code_fun F a_1)) = refl (expr.mul a a_1),
      rwr ih_a, rwr ih_a_1 }
  end,    
assume x y,  
  equiv.mk (encode_expr F x y) 
      (is_equiv.adjointify (encode_expr F x y) (decode_expr F x y) (rinv x y) (linv x y))         

@[hott, instance]
def is_set_expr {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_set (expr F) :=
begin 
  apply is_trunc_succ_intro, intros x y, 
  apply is_trunc_equiv_closed_rev -1 (expr_eq_equiv_code F x y), 
  fapply code_expr.rec F, any_goals { apply_instance },
  { intros a b IH, exact IH },
  { intros, change is_prop ((code_expr F x₁ y₁) × (code_expr F x₂ y₂)), 
    exact @is_trunc_prod _ _ _ a a_1 },
  { intros, change is_prop ((code_expr F x₁ y₁) × (code_expr F x₂ y₂)), 
    exact @is_trunc_prod _ _ _ a a_1 }
end     

@[hott, reducible]
def set_expr {J : Set} [precategory J] (F : J ⥤ CommRing) : Set :=
  Set.mk (expr F) (is_set_expr F)

@[hott]
inductive ring_colim_rel {J : Set.{u'}} [precategory.{v'} J] (F : J ⥤ CommRing.{u}) : 
  expr F → expr F → Type (max u' v' u)
-- Make it an equivalence relation:
| refl : Π (x), ring_colim_rel x x
| symm : Π (x y) (h : ring_colim_rel x y), ring_colim_rel y x
| trans : Π (x y z) (h : ring_colim_rel x y) (k : ring_colim_rel y z), ring_colim_rel x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (r : F.obj j), 
        ring_colim_rel (expr.x_ j' ((F.map f).1 r)) (expr.x_ j r)
-- Then one relation per operation, describing the interaction with `expr.x_`
| zero : Π (j), ring_colim_rel (expr.x_ j 0) (expr.zero F)
| one : Π (j), ring_colim_rel (expr.x_ j 1) (expr.one F)
| neg : Π (j) (x : F.obj j), ring_colim_rel (expr.x_ j (-x)) (expr.neg (expr.x_ j x))
| add : Π (j) (x y : F.obj j), ring_colim_rel (expr.x_ j (x + y)) 
                                              (expr.add (expr.x_ j x) (expr.x_ j y))
| mul : Π (j) (x y : F.obj j), ring_colim_rel (expr.x_ j (x * y)) 
                                              (expr.mul (expr.x_ j x) (expr.x_ j y))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : ring_colim_rel x x'), ring_colim_rel (expr.neg x) (expr.neg x')
| add_1 : Π (x x' y) (r : ring_colim_rel x x'), ring_colim_rel (expr.add x y) (expr.add x' y)
| add_2 : Π (x y y') (r : ring_colim_rel y y'), ring_colim_rel (expr.add x y) (expr.add x y')
| mul_1 : Π (x x' y) (r : ring_colim_rel x x'), ring_colim_rel (expr.mul x y) (expr.mul x' y)
| mul_2 : Π (x y y') (r : ring_colim_rel y y'), ring_colim_rel (expr.mul x y) (expr.mul x y')
-- And one relation per axiom
| zero_add      : Π (x), ring_colim_rel (expr.add (expr.zero F) x) x
| add_zero      : Π (x), ring_colim_rel (expr.add x (expr.zero F)) x
| one_mul       : Π (x), ring_colim_rel (expr.mul (expr.one F) x) x
| mul_one       : Π (x), ring_colim_rel (expr.mul x (expr.one F)) x
| add_left_neg  : Π (x), ring_colim_rel (expr.add (expr.neg x) x) (expr.zero F)
| add_comm      : Π (x y), ring_colim_rel (expr.add x y) (expr.add y x)
| mul_comm      : Π (x y), ring_colim_rel (expr.mul x y) (expr.mul y x)
| add_assoc     : Π (x y z), ring_colim_rel (expr.add (expr.add x y) z) 
                                            (expr.add x (expr.add y z))
| mul_assoc     : Π (x y z), ring_colim_rel (expr.mul (expr.mul x y) z) 
                                            (expr.mul x (expr.mul y z))
| left_distrib  : Π (x y z), ring_colim_rel (expr.mul x (expr.add y z)) 
                                            (expr.add (expr.mul x y) (expr.mul x z))
| right_distrib : Π (x y z), ring_colim_rel (expr.mul (expr.add x y) z) 
                                            (expr.add (expr.mul x z) (expr.mul y z))   

@[hott, reducible]
def ring_colim_mere_rel {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  set_expr F → set_expr F → trunctype -1 :=
λ x y : set_expr F, ∥ring_colim_rel F x y∥ 

@[hott, instance]
def rcm_rel_refl {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_reflexive (λ x y : set_expr F, ring_colim_mere_rel F x y) :=
begin apply is_reflexive.mk, intro x, exact tr (ring_colim_rel.refl x) end  

@[hott, instance]
def rcm_rel_symm {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_symmetric (λ x y : set_expr F, ring_colim_mere_rel F x y) :=
begin 
  apply is_symmetric.mk, intros x y, 
  apply trunc.rec, intro r,
  exact tr (ring_colim_rel.symm x y r) 
end 

@[hott, instance]
def rcm_rel_trans {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_transitive (λ x y : set_expr F, ring_colim_mere_rel F x y) :=
begin 
  apply is_transitive.mk, intros x y z, 
  apply @trunc.rec -1 _ (λ r : ring_colim_mere_rel F x y, (ring_colim_mere_rel F y z) ->
                                                          (ring_colim_mere_rel F x z)),
  intro r, apply trunc.rec, intro s,                                                         
  exact tr (ring_colim_rel.trans x y z r s) 
end 

@[hott, instance]
def rcm_rel_equiv {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_equivalence (λ x y : set_expr F, ring_colim_mere_rel F x y) :=
begin 
  apply is_equivalence.mk, 
  exact (rcm_rel_refl F).refl, exact (rcm_rel_symm F).symm, exact (rcm_rel_trans F).trans
end  

@[hott]
def ring_colim_set {J : Set} [precategory J] (F : J ⥤ CommRing) : Set :=
  set_quotient (ring_colim_mere_rel F)

@[hott, reducible]
def ring_colim_ops {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  comm_ring_ops (ring_colim_set F) :=
begin
  let R := ring_colim_set F, let rel := ring_colim_rel F, let mrel := ring_colim_mere_rel F,
  fapply comm_ring_ops.mk, 
  { fapply set_quotient.elim2, 
    { intros x y, exact set_class_of mrel (expr.add x y) },
    { intros a a' b, apply trunc.rec, intro r, 
      apply quot_rel_to_setquot_eq mrel, hsimp,         
      exact tr (ring_colim_rel.add_1 a a' b r) },
    { intros a b b', apply trunc.rec, intro r, 
      apply quot_rel_to_setquot_eq mrel, hsimp, 
      exact tr (ring_colim_rel.add_2 a b b' r) } }, --add
  { exact set_class_of mrel (expr.zero F) }, --zero
  { fapply set_quotient.elim, 
    { intro x, exact set_class_of mrel (expr.neg x) },
    { intros a a', apply trunc.rec, intro r, 
      apply quot_rel_to_setquot_eq mrel, hsimp, 
      exact tr (ring_colim_rel.neg_1 a a' r) } }, --neg
  { fapply set_quotient.elim2, 
    { intros x y, exact set_class_of mrel (expr.mul x y) },
    { intros a a' b, apply trunc.rec, intro r, 
      apply quot_rel_to_setquot_eq mrel, hsimp, 
      exact tr (ring_colim_rel.mul_1 a a' b r) },
    { intros a b b', apply trunc.rec, intro r, 
      apply quot_rel_to_setquot_eq mrel, hsimp, 
      exact tr (ring_colim_rel.mul_2 a b b' r) } }, --mul
  { exact set_class_of mrel (expr.one F) }  --one
end     

@[hott]
def ring_colim_str {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  comm_ring (ring_colim_set F) :=
begin 
  let R := ring_colim_set F, let rel := ring_colim_rel F, let mrel := ring_colim_mere_rel F,
  fapply comm_ring_mk,
  { exact ring_colim_ops F }, 
  { fapply comm_ring_laws.mk, 
    { apply set_quotient.prec3, intros x y z, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.add_assoc x y z) }, --add_assoc
    { apply set_quotient.prec, intro x, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.zero_add x) }, --zero_add
    { apply set_quotient.prec, intro x, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.add_zero x) }, --add_zero
    { apply set_quotient.prec, intro x, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.add_left_neg x) }, --add_neg
    { apply set_quotient.prec2, intros x y, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.add_comm x y) }, --add_comm
    { apply set_quotient.prec3, intros x y z, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.mul_assoc x y z) }, --mul_assoc
    { apply set_quotient.prec, intro x, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.one_mul x) }, --one_mul
    { apply set_quotient.prec, intro x, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.mul_one x) }, --mul_one
    { apply set_quotient.prec2, intros x y, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.mul_comm x y) }, --mul_comm
    { apply set_quotient.prec3, intros x y z, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.left_distrib x y z) }, --right_distr
    { apply set_quotient.prec3, intros x y z, apply quot_rel_to_setquot_eq mrel,
      exact tr (ring_colim_rel.right_distrib x y z)  } } --left_distr
end  

@[hott, reducible]
def ring_cocone {J : Set} [precategory J] (F : J ⥤ CommRing) : cocone F :=
begin
  let mR := ring_colim_mere_rel F,
  fapply cocone.mk,
  /- The limit cocone vertex set -/
  { exact CommRing.mk (ring_colim_set F) (ring_colim_str F) },
  { fapply nat_trans.mk, 
    /- the leg homomorphisms of the limit cocone -/
    { intro j, fapply elem_pred, -- ring homomorphisms consist of a set map satisfying laws
      { intro r, exact set_class_of mR (expr.x_ j r) },
      { change is_ring_hom _ _ (λ r, set_class_of mR (expr.x_ j r)), fapply is_ring_hom.mk, 
        { apply quot_rel_to_setquot_eq mR, exact tr (ring_colim_rel.one F j) },
        { intros a b, apply quot_rel_to_setquot_eq mR, exact tr (ring_colim_rel.mul j a b) },
        { apply quot_rel_to_setquot_eq mR, exact tr (ring_colim_rel.zero F j) },
        { intros a b, apply quot_rel_to_setquot_eq mR, exact tr (ring_colim_rel.add j a b) } } },
    { intros j k f, apply hom_eq_C_std _ _, apply eq_of_homotopy, --diagram compatibility
      intro r, apply quot_rel_to_setquot_eq mR, exact tr (ring_colim_rel.map j k f r) } }
end

/- To show that the ring cocone constructed above descends to any other cocone over the same
   diagram we need a variant of the left-adjointness of the free ring construction to the 
   forgetful functor. -/
@[hott, reducible]
def ring_cocone_desc {J : Set} [precategory J] {F : J ⥤ CommRing} (S : cocone F) :
  (ring_cocone F).X ⟶ S.X :=
begin
  fapply elem_pred, 
    { fapply set_quotient.elim, 
      { intro x, hinduction x, --the underlying set-map
        { exact (S.π.app j).1 r }, 
        { exact @comm_ring.zero S.X S.X.str },
        { exact @comm_ring.one S.X S.X.str },
        { exact @comm_ring.neg S.X S.X.str ih },
        { exact @comm_ring.add S.X S.X.str ih_a ih_a_1 },
        { exact @comm_ring.mul S.X S.X.str ih_a ih_a_1 } },
      { intros x y, apply trunc.rec, intro H, hinduction H, --well-definedness
        { refl }, { rwr ih }, { rwr ih_h, rwr <- ih_k }, 
        { hsimp, exact homotopy_of_eq ((ap sigma.fst (S.π.naturality f))) r }, 
        { hsimp, exact (S.π.app j).2.map_zero },
        { hsimp, exact (S.π.app j).2.map_one }, 
        { hsimp, exact comm_ring_hom.map_neg (S.π.app j).2 x }, 
        { hsimp, exact (S.π.app j).2.map_add x y }, 
        { hsimp, exact (S.π.app j).2.map_mul x y }, 
        any_goals { hsimp at ih, hsimp, rwr ih }, 
        { hsimp, exact @comm_ring.zero_add S.X S.X.str _ }, 
        { hsimp, exact @comm_ring.add_zero S.X S.X.str _ }, 
        { hsimp, exact @comm_ring.one_mul S.X S.X.str _ }, 
        { hsimp, exact @comm_ring.mul_one S.X S.X.str _ },
        { hsimp, exact @comm_ring.add_left_inv S.X S.X.str _ }, 
        { hsimp, exact @comm_ring.add_comm S.X S.X.str _ _ }, 
        { hsimp, exact @comm_ring.mul_comm S.X S.X.str _ _ }, 
        { hsimp, exact @comm_ring.add_assoc S.X S.X.str _ _ _ }, 
        { hsimp, exact @comm_ring.mul_assoc S.X S.X.str _ _ _ },
        { hsimp, exact @comm_ring.left_distrib S.X S.X.str _ _ _ }, 
        { hsimp, exact @comm_ring.right_distrib S.X S.X.str _ _ _ } } },
    { fapply is_ring_hom.mk, any_goals { refl }, 
      { apply set_quotient.prec2, intros x y, hsimp, refl }, 
      { apply set_quotient.prec2, intros x y, hsimp, refl } }  
end       

@[hott, reducible]
def ring_cocone_is_colimit {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  is_colimit (ring_cocone F) :=
begin 
  fapply is_colimit.mk, 
  { intro S, exact ring_cocone_desc S },  --descending to another cocone
  { intros S j, apply hom_eq_C_std _ _, apply eq_of_homotopy, --diagram compatibility
      intro r, refl },
  { intros S d H, apply hom_eq_C_std _ _, apply eq_of_homotopy, 
    have Hr : Π (j : J) (r : F.obj j), d.1 (((ring_cocone F).π.app j).1 r) = (S.π.app j).1 r, from
      begin 
        intros j, apply homotopy_of_eq, 
        change (λ x, (((ring_cocone F).π.app j).1 ≫ d.1) x) = λ x, (S.π.app j).1 x,
        have H1 : ((ring_cocone F).π.app j).1 ≫ d.1 = (((ring_cocone F).π.app j) ≫ d).1, from
          rfl,
        rwr H1, rwr ap sigma.fst (H j)
      end, 
    let mrel := ring_colim_mere_rel F,  
    apply set_quotient.prec, intro x, hinduction x, 
    { change d.1 (((ring_cocone F).π.app j).1 r) = (ring_cocone_desc S).1 
                                   (set_class_of (ring_colim_mere_rel F) (expr.x_ j r)),
      rwr Hr j r },
    { change d.1 0 = (ring_cocone_desc S).1 0, rwr d.2.map_zero },
    { change d.1 1 = (ring_cocone_desc S).1 1, rwr d.2.map_one },
    { change d.1 (-(set_class_of mrel a)) = (ring_cocone_desc S).1 (-(set_class_of mrel a)), 
      rwr comm_ring_hom.map_neg d.2, rwr comm_ring_hom.map_neg (ring_cocone_desc S).2, 
      rwr ih },
    { change d.1 ((set_class_of mrel a) + (set_class_of mrel a_1)) =
             (ring_cocone_desc S).1 ((set_class_of mrel a) + (set_class_of mrel a_1)), 
      rwr d.2.map_add, rwr (ring_cocone_desc S).2.map_add, rwr ih_a, rwr ih_a_1 },
    { change d.1 ((set_class_of mrel a) * (set_class_of mrel a_1)) =
             (ring_cocone_desc S).1 ((set_class_of mrel a) * (set_class_of mrel a_1)), 
      rwr d.2.map_mul, rwr (ring_cocone_desc S).2.map_mul, rwr ih_a, rwr ih_a_1 } }
end 

@[hott, reducible]
def ring_colimit_cocone {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  colimit_cocone F :=
colimit_cocone.mk (ring_cocone F) (ring_cocone_is_colimit F)

@[hott, instance]
def ring_has_colimit {J : Set} [precategory J] (F : J ⥤ CommRing) : 
  has_colimit F :=
has_colimit.mk (ring_colimit_cocone F)

@[hott, instance]
def ring_has_colimits_of_shape (J : Set) [precategory J] : 
  has_colimits_of_shape J CommRing :=
has_colimits_of_shape.mk (λ F, ring_has_colimit F) 

@[hott, instance]
def ring_has_colimits : has_colimits CommRing :=
  has_colimits.mk (λ J pJ, @ring_has_colimits_of_shape J pJ)

end algebra

end hott