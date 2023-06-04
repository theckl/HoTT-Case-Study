import sets.subset categories.colimits categories.pullback

universes v v' u u' w
hott_theory

namespace hott
open hott.subset hott.precategories hott.categories hott.categories.limits hott.is_trunc 
     categories.adjoints hott.set hott.trunc hott.categories.pullbacks
     hott.categories.colimits

namespace categories.boolean

/- Distributivity of unions and intersections of subobjects, and uniqueness of 
   complements, holds if (finite) unions are stable under pullbacks. -/
@[hott]
class has_stable_unions (C : Category) [has_pullbacks C] [has_unions C] :=
  (has_stab_unions : Π {c d : C} (f : c ⟶ d) {J : Set} (i : J -> subobject d), 
     pullback_subobject f (@subobject.union C d J i (has_union_of_has_unions _)) = 
              @subobject.union C c J ((λ b : subobject d, pullback_subobject f b) ∘ i) _)

@[hott]
class has_stable_fin_unions (C : Category) [has_pullbacks C] [has_fin_unions C] :=
  (has_stab_fin_unions : Π {c d : C} (f : c ⟶ d) (a b : subobject d), 
     pullback_subobject f (a ∪ b) = (pullback_subobject f a) ∪ (pullback_subobject f b))

@[hott, instance]
def has_stable_fin_unions_of_stable_unions {C : Category} [has_pullbacks C] 
  [H : has_unions C] [Hs : has_stable_unions C] : 
  @has_stable_fin_unions C _ (@has_fin_unions_of_has_unions C H) :=
begin
  fapply has_stable_fin_unions.mk, intros c d f a b, 
  change pullback_subobject f (subobject.union (fin_map_of_list [a, b])) = _,
  rwr @has_stable_unions.has_stab_unions C _ _ Hs _ _ f _ (fin_map_of_list [a, b]),
  have p : (λ (b : subobject d), pullback_subobject f b) ∘ fin_map_of_list [a, b] =
              fin_map_of_list [pullback_subobject f a, pullback_subobject f b], from 
  begin 
    apply eq_of_homotopy, intro n, hinduction n with n ineq, hinduction n,
    { have q : fin_map_of_list [a, b] ⟨0, ineq⟩ = b, from 
        begin hsimp, rwr dite_false ((nat.succ_ne_zero 0) ∘ eq.inverse) end,
      change pullback_subobject f (fin_map_of_list [a, b] ⟨0, ineq⟩) = _,
      rwr q },
    { hinduction n, 
    {  have r : fin_map_of_list [a, b] ⟨1, ineq⟩ = a, from 
         begin hsimp, apply dite_true (idpath 1), apply_instance end,
       change pullback_subobject f (fin_map_of_list [a, b] ⟨1, ineq⟩) = _,
       rwr r },
    { change _ < nat.succ 1 at ineq, 
      hinduction nat.not_lt_zero n (nat.le_of_succ_le_succ (nat.le_of_succ_le_succ ineq)) } }
  end, 
  rwr p
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
def inter_distrib {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C] 
  [H : has_stable_fin_unions C] (a b c : subobject d) : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) :=
begin
  change subobj_subobj_trans _ _ = _, rwr H.has_stab_fin_unions, 
  rwr subobj_trans_union a (pullback_subobject a.hom b) (pullback_subobject a.hom c)
end 

@[hott]
def union_distrib {C : Category} {d : C} [has_pullbacks C] [has_fin_unions C] 
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
def complement_is_unique {C : Category} {c : C} [has_pullbacks C] [has_fin_unions C] 
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
class object_has_complements {C : Category} [has_pullbacks C] [has_fin_unions C] 
  [has_stable_fin_unions C] (c : C) :=
(compl : Π (a : subobject c), complement a) 

@[hott, instance] 
def has_compl_of_obj_has_compl {C : Category} (c : C) [has_pullbacks C] [has_fin_unions C] 
  [has_stable_fin_unions C] [H : object_has_complements c] :
  @has_complement (subobject c) :=
has_complement.mk (λ a : subobject c, (@object_has_complements.compl _ _ _ _ c H a).na)

@[hott]
class has_complements (C : Category) [has_pullbacks C] [has_fin_unions C] 
  [has_stable_fin_unions C] :=
(compl : Π {c : C}, object_has_complements c)

@[hott, instance]
def obj_has_compl_of_has_complements {C : Category} [has_pullbacks C] [has_fin_unions C] 
  [has_stable_fin_unions C] [H : has_complements C] (c : C) :
  object_has_complements c :=
object_has_complements.mk (@has_complements.compl _ _ _ _ H c).compl  

/- Subsets of a set (in the category of sets) have complements if the `∈`-relation is 
   decidable. -/
@[hott]
class has_decidable_elem (A : Set) :=
  (lem_elem : Π (S : Subset A) (a : A), decidable (a ∈ S))

/-
@[hott, instance]
def subsets_have_complements (A : Set) [has_decidable_elem A] : 
  has_complements (@subobject Set_Category A) :=
-/

end categories.boolean

end hott 