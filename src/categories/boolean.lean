import sets.subset categories.colimits categories.pullback

universes v v' u u' w
hott_theory

namespace hott
open hott.subset hott.precategories hott.categories hott.categories.limits hott.is_trunc 
     categories.adjoints hott.set hott.trunc hott.categories.pullbacks
     hott.categories.colimits

namespace categories.boolean

/- Distributivity of unions and intersections of subobjects, and uniqueness of 
   complements, holds if (finite) unions are stable under pullbacks. 
   
   We avoid different routes to instances of pullbacks by not extending from 
   `has_pullbacks` and introducing a class combining pullbacks and stable images,
   so that we can use `has_stable_unions` and `has_stable_fin_unions` without providing 
   `has_pullbacks` in models. -/
@[hott]
class has_stable_unions (C : Category) [has_pullbacks C] extends has_unions C :=
  (has_stab_unions : Π {c d : C} (f : c ⟶ d) {J : Set} (i : J -> subobject d), 
     pullback_subobject f (@subobject.union C d J i (has_union_of_has_unions _)) = 
              @subobject.union C c J ((λ b : subobject d, pullback_subobject f b) ∘ i) _)

@[hott]
class has_pb_and_stab_unions (C : Category) :=
  (pb_stab_unions : Σ (H : has_pullbacks C), has_stable_unions C)

@[hott, instance]
def has_stab_unions_of_pb_stab_unions (C : Category) [H : has_pb_and_stab_unions C] :
  @has_stable_unions C H.pb_stab_unions.1 := H.pb_stab_unions.2  

@[hott]
class has_stable_fin_unions (C : Category) [has_pullbacks C] extends has_fin_unions C :=
  (has_stab_fin_unions :  Π {a b : C} (f : a ⟶ b) {n : ℕ} (i : fin_Set n -> subobject b), 
     pullback_subobject f (subobject.union i) = 
                       subobject.union ((λ d : subobject b, pullback_subobject f d) ∘ i)) 

@[hott]
class has_pb_and_fin_stab_unions (C : Category) :=
  (pb_stab_fin_unions : Σ (H : has_pullbacks C), has_stable_fin_unions C)

@[hott, instance]
def has_stab_fin_unions_of_pb_fin_stab_unions (C : Category) 
  [H : has_pb_and_fin_stab_unions C] :
  @has_stable_fin_unions C H.pb_stab_fin_unions.1 := H.pb_stab_fin_unions.2  

@[hott, instance]
def has_stable_fin_unions_of_stable_unions {C : Category} [has_pullbacks C] 
  [Hs : has_stable_unions C] : has_stable_fin_unions C :=
@has_stable_fin_unions.mk _ _ _ (λ (a b : C) (f : a ⟶ b) (n : ℕ) 
  (i : fin_Set n -> subobject b), @has_stable_unions.has_stab_unions _ _ Hs _ _ f _ i)

@[hott]
def pullback_union_eq {C : Category} [has_pullbacks C] [Hs : has_stable_fin_unions C] : 
  Π {a b : C} (f : a ⟶ b) (d d' : subobject b),
    pullback_subobject f (d ∪ d') = pullback_subobject f d ∪ pullback_subobject f d' :=
begin 
  intros a b f d d',
  change pullback_subobject f (subobject.union (fin_map_of_list [d, d'])) = _,
  let q := has_stable_fin_unions.has_stab_fin_unions f (fin_map_of_list [d, d']), rwr q,
  have p : (λ (d : subobject b), pullback_subobject f d) ∘ fin_map_of_list [d, d'] =
              fin_map_of_list [pullback_subobject f d, pullback_subobject f d'], from 
  begin 
    apply eq_of_homotopy, intro n, hinduction n with n ineq, hinduction n,
    { have q : fin_map_of_list [d, d'] ⟨0, ineq⟩ = d', from 
        begin hsimp, rwr dite_false ((nat.succ_ne_zero 0) ∘ eq.inverse) end,
      change pullback_subobject f (fin_map_of_list [d, d'] ⟨0, ineq⟩) = _,
      rwr q },
    { hinduction n, 
    {  have r : fin_map_of_list [d, d'] ⟨1, ineq⟩ = d, from 
         begin hsimp, apply dite_true (idpath 1), apply_instance end,
       change pullback_subobject f (fin_map_of_list [d, d'] ⟨1, ineq⟩) = _,
       rwr r },
    { change _ < nat.succ 1 at ineq, 
      hinduction nat.not_lt_zero n (nat.le_of_succ_le_succ (nat.le_of_succ_le_succ ineq)) } }
  end, 
  rwr p
end

@[hott]
def stable_bottom {C : Category} [has_pullbacks C] [Hs : has_stable_fin_unions C] : 
  Π {a b : C} (f : a ⟶ b), pullback_subobject f (bottom_subobject b) = 
                                                                bottom_subobject a :=
begin 
  intros a b f,
  change pullback_subobject f (subobject.union (empty_fin_Set_map (subobject b))) = _,
  rwr @has_stable_fin_unions.has_stab_fin_unions _ _ Hs _ _ f _ 
                                     (empty_fin_Set_map (subobject b)),
  rwr empty_fin_Set_map_comp 
end


/- Absorption laws and distributive laws in the lattice of subobjects. -/
@[hott]
def absorption_inter {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C]
  (a b : subobject d) : a ∩ (a ∪ b) = a :=
begin
  fapply subobj_antisymm,
  { exact subobj_inter_linc _ _ },
  { fapply subobj_inter_lift, 
    { exact 𝟙 a },
    { exact subobj_union_linc _ _ } }
end

@[hott]
def absorption_union {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C]
  (a b : subobject d) : a ∪ (a ∩ b) = a :=
begin
  fapply subobj_antisymm,
  { fapply lift_to_union,
    { exact 𝟙 a },
    { exact subobj_inter_linc _ _ } },
  { exact subobj_union_linc _ _ }
end

@[hott]
def subobj_trans_pullback {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C] 
  (a c : subobject d ) (b : subobject a.obj) : 
  subobj_subobj_trans a b ≼ c -> b ≼ pullback_subobject a.hom c :=
begin
  intro trans_ineq, fapply pb_subobj_lift, exact trans_ineq.hom_obj, rwr trans_ineq.fac
end

@[hott]
def subobj_trans_union {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C] : 
  Π (a : subobject d) (b c : subobject a.obj),
  subobj_subobj_trans a (b ∪ c) = (subobj_subobj_trans a b) ∪ (subobj_subobj_trans a c) :=
begin
  intros a b c, fapply univ_char_of_union, 
  { exact subobj_subobj_trans_pres_hom a b (b ∪ c) (subobj_union_linc _ _) },
  { exact subobj_subobj_trans_pres_hom a c (b ∪ c) (subobj_union_rinc _ _) },
  { intros c' bc' cc', apply (λ i, subobj_trans i (subobj_inter_rinc a c')), 
    apply subobj_subobj_trans_pres_hom a (b ∪ c), 
    exact lift_to_union (subobj_trans_pullback _ _ _ bc') 
                        (subobj_trans_pullback _ _ _ cc') }
end

@[hott]
def inter_distrib {C : Category} {d : C} [has_pullbacks C] 
  [H : has_stable_fin_unions C] (a b c : subobject d) : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) :=
begin
  change subobj_subobj_trans _ _ = _, rwr pullback_union_eq a.hom b c, 
  rwr subobj_trans_union a (pullback_subobject a.hom b) (pullback_subobject a.hom c)
end 

@[hott]
def union_distrib {C : Category} {d : C} [has_pullbacks C]
  [has_stable_fin_unions C] (a b c : subobject d) : a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c) :=
begin
  have p₁ : a ∪ (b ∩ c) = (a ∪ (a ∩ c)) ∪ (b ∩ c), from 
    (ap (λ a' : subobject d, a' ∪ (b ∩ c)) (absorption_union a c)⁻¹),
  rwr p₁, rwr union_assoc, rwr subobj_inter_symm a c; rwr subobj_inter_symm b c,
  rwr <- inter_distrib c a b, 
  have p₂ : a ∪ c ∩ (a ∪ b) = a ∩ (a ∪ b) ∪ c ∩ (a ∪ b), from 
    (ap (λ a' : subobject d, a' ∪ c ∩ (a ∪ b)) (absorption_inter a b)⁻¹),
  rwr p₂, rwr subobj_inter_symm a (a ∪ b); rwr subobj_inter_symm c (a ∪ b), 
  rwr <- inter_distrib (a ∪ b) a c 
end


/- Now we introduce complements of subobjects, prove their uniqueness and introduce the
   notation `𝒞`. -/
@[hott]
structure complement {C : Category} {c : C} [has_pullbacks C] [has_fin_unions C] 
  (a : subobject c) :=
(na : subobject c)
(union : a ∪ na = top_subobject c)
(inter : a ∩ na = bottom_subobject c)

/- Complements are unique if finite unions are stable under pullbacks. -/
@[hott]
def complement_is_unique {C : Category} {c : C} [has_pullbacks C] 
  [has_stable_fin_unions C] (a : subobject c) : 
  Π (ca ca' : complement a), ca.na = ca'.na :=
begin
  intros ca ca', fapply subobj_antisymm, 
  { rwr <- top_inter_absorb ca.na, rwr <- ca'.union, 
    rwr inter_distrib ca.na a ca'.na, rwr subobj_inter_symm ca.na a, rwr ca.inter, 
    rwr bottom_union_absorb (ca.na ∩ ca'.na) , exact subobj_inter_rinc _ _ },
  { rwr <- top_inter_absorb ca'.na, rwr <- ca.union, rwr inter_distrib ca'.na a ca.na, 
    rwr subobj_inter_symm, rwr ca'.inter, rwr bottom_union_absorb,
    exact subobj_inter_rinc _ _ } 
end

/- Now we can define a class of categories that have complements to all subobjects of 
   all objects. -/
@[hott]
class has_complements (C : Category) [has_pullbacks C] extends has_stable_fin_unions C :=
  (compl : Π {c : C} (a : subobject c), complement a)

@[hott]
class has_pb_and_compl (C : Category) :=
  (pb_and_compl : Σ (H : has_pullbacks C), has_complements C)

@[hott, instance] 
def has_compl_of_obj_has_compl {C : Category} (c : C) [has_pullbacks C] 
  [H : has_complements C] : @has_complement (subobject c) :=
has_complement.mk (λ a : subobject c, (@has_complements.compl _ _ H c a).na)

/- We need some calculation rules for complements. -/
@[hott]
def top_compl {C : Category} [has_pullbacks C] [H : has_complements C] {a : C} 
  (c : subobject a) : c ∪ 𝒞(c) = top_subobject a :=
(has_complements.compl c).union

@[hott]
def bottom_compl {C : Category} [has_pullbacks C] [H : has_complements C] {a : C} 
  (c : subobject a) : c ∩ 𝒞(c) = bottom_subobject a :=
(has_complements.compl c).inter

@[hott]
def compl_compl {C : Category} [has_pullbacks C] [H : has_complements C] {a : C} 
  (c : subobject a) : 𝒞(𝒞(c)) = c :=
begin
  have t : 𝒞(c) ∪ c = top_subobject a, by rwr union_comm; exact top_compl _,
  have b : 𝒞(c) ∩ c = bottom_subobject a, by rwr subobj_inter_symm; exact bottom_compl _,
  let CCc : complement 𝒞(c) := complement.mk c t b,
  exact complement_is_unique _ _ CCc
end

@[hott]
def compl_inter_bot {C : Category} [has_pullbacks C] [H : has_complements C] {a : C} 
  {c c' : subobject a} : c ≼ c' -> c ∩ 𝒞(c') = bottom_subobject a :=
begin
  intro i, fapply subobj_antisymm, 
  { rwr <- bottom_compl c', apply subobj_inter_lift, 
    { apply @subobj_trans _ _ _ c _, exact subobj_inter_linc _ _, exact i },
    { exact subobj_inter_rinc _ _ } },
  { exact bottom_subobj_prop _ }
end

@[hott]
def contra_pos_compl {C : Category} [has_pullbacks C] [has_complements C] {a : C} 
  {c c' : subobject a} : (c ≼ c') -> (𝒞(c') ≼ 𝒞(c)) :=
begin
  intro i, rwr <- top_inter_absorb 𝒞(c'), rwr <- top_compl c, 
  rwr inter_distrib, rwr <- subobj_inter_symm c 𝒞(c'), rwr compl_inter_bot i,
  rwr bottom_union_absorb, exact subobj_inter_rinc _ _
end

@[hott]
def contra_pos_compl_inv {C : Category} [has_pullbacks C] [has_complements C] {a : C} 
  {c c' : subobject a} : (𝒞(c') ≼ 𝒞(c)) -> (c ≼ c') :=
begin
  intro Ci, rwr <- compl_compl c, rwr <- compl_compl c',
  exact contra_pos_compl Ci
end


/- We introduce now the hierarchy of categories that can hold models of first-order 
   theories over first-order signatures. 
   
   We only assume the existence of limits along diagrams in universe 0 because 
   otherwise Lean does not deduce an instance of `has_pullback` from `has_limits`.
   This is enough for all ready-made diagrams like orthogonal wedges and parallel pairs,
   but it may not be enough when diagrams are induced e.g. by the lattice structure of
   opene subsets of a topological space. -/
@[hott]
class is_Cartesian (C : Category.{u v}) :=
  (has_limits : has_limits.{v u 0 0} C)

@[hott, instance]
def has_lim_of_is_Cart (C : Category) [H : is_Cartesian C] : has_limits C :=
  H.has_limits

@[hott]
class is_regular (C : Category) extends is_Cartesian C :=
  (has_stable_images : has_stable_images C)
    
@[hott, instance]
def has_stable_images_of_is_regular (C : Category) [H : is_regular C] : 
  has_stable_images C := H.has_stable_images

@[hott]
class is_coherent (C : Category) extends is_regular C :=
  (has_stable_fin_unions : has_stable_fin_unions C)

@[hott]
class is_geometric (C : Category) extends is_regular C :=
  (has_stable_unions : has_stable_unions C)

@[hott, instance]
def has_stable_unions_of_is_geometric (C : Category) [H : is_geometric C] : 
  has_stable_unions C := H.has_stable_unions

@[hott]
class is_Heyting (C : Category) extends is_coherent C :=
  (has_all_of_fibers : has_all_of_fibers C)
    
@[hott, instance]
def has_all_of_fibers_of_is_Heyting (C : Category) [H : is_Heyting C] : 
  has_all_of_fibers C := H.has_all_of_fibers 

@[hott]
class is_Boolean (C : Category) extends is_coherent C :=
  (has_complements : has_complements C)
    
@[hott, instance]
def has_complements_of_is_Boolean (C : Category) [H : is_Boolean C] : 
  @has_complements C (@has_pullbacks_of_has_limits C H.to_is_Cartesian.has_limits) := 
H.has_complements

/- Complements are stable under pullbacks. -/
@[hott]
def stable_complements (C : Category) [H : is_Boolean C] :
  Π {a b : C} (f : a ⟶ b) (d : subobject b), 
  pullback_subobject f (𝒞(d)) = 𝒞(pullback_subobject f d ) :=
begin
  intros a b f d, 
  have p : d ∪ 𝒞(d) = top_subobject b, from top_compl d,
  have t : (pullback_subobject f d) ∪ (pullback_subobject f 𝒞(d)) = 
                                                             top_subobject a, from
  begin rwr <- pullback_union_eq f, rwr top_compl d, exact stable_top f end,
  have b : (pullback_subobject f d) ∩ pullback_subobject f 𝒞(d) = 
                                                            bottom_subobject a, from
    begin rwr <- pullback_inter_eq f, rwr bottom_compl, exact stable_bottom f end,
  let Cfd : complement (pullback_subobject f d) := 
                                   complement.mk (pullback_subobject f 𝒞(d)) t b,
  exact complement_is_unique _ Cfd _
end

/- Boolean categories are Heyting. -/  
@[hott, instance]
def all_of_fibs_of_Boolean (C : Category) [H : is_Boolean C] : 
  has_all_of_fibers C :=
begin
  apply has_all_of_fibers.mk, intros a b f,
  apply has_all_of_fiber.mk, apply has_right_adjoint.mk, fapply is_left_adjoint.mk,
  { fapply precategories.functor.mk, 
    { intro c, exact 𝒞((ex_fib f).obj 𝒞(c)) },
    { intros c c' i, apply contra_pos_compl, exact (ex_fib f).map (contra_pos_compl i) },
    { intro c, exact is_prop.elim _ _ },
    { intros c d e f g, exact is_prop.elim _ _ } },
  { apply adjoint_hom_to_adjoint, fapply adjoint_functors_on_hom.mk,
    { intros c d, fapply bijection_of_props,
      { intro i₁, apply contra_pos_compl_inv, rwr compl_compl, 
        apply ex_fib_left_adj, rwr stable_complements, exact contra_pos_compl i₁ },
      { intro i₂, apply contra_pos_compl_inv, change _ ≼ 𝒞(pullback_subobject f c), 
        rwr <- stable_complements, apply ex_fib_right_adj, apply contra_pos_compl_inv,
        rwr compl_compl, exact i₂ } },
    { intros c d c' h g, exact is_prop.elim _ _ },
    { intros c d d' g h, exact is_prop.elim _ _ } }
end

@[hott, instance]
def is_Heyting_of_is_Boolean (C : Category) [H : is_Boolean C] :
  is_Heyting C :=
begin fapply is_Heyting.mk, apply_instance end

end categories.boolean

end hott 