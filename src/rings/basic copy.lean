import hott.algebra.ring sets.basic categories.examples categories.cat_limits init2 types2
       hott.types.prod hott.algebra.relation categories.cat_colimits

universes u u' v w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set subset categories hott.trunc
     hott.category_theory.limits hott.sigma hott.prod hott.relation 
     hott.category_theory.colimits hott.ulift list

namespace algebra

/- We construct the category of rings as a full subcategory of a first-order signature 
   category of operations on a set and laws governing them, and construct objects of that
   category from a `comm_ring` structure on a set. 
   
   We first need to define the first-order signature. -/
@[hott]
inductive ring_ops : Type 0 
| add : ring_ops
| zero : ring_ops 
| neg : ring_ops 
| mul : ring_ops 
| one : ring_ops

@[hott]
def ring_ops_is_set : is_set ring_ops := 
begin
  let f : ring_ops -> ℕ := 
    begin intro o, hinduction o, exact 0, exact 1, exact 2, exact 3, exact 4 end,
  have inj_f : ∀ o₁ o₂ : ring_ops, f o₁ = f o₂ -> o₁ = o₂, from 
  begin
    intros o₁ o₂, hinduction o₁; hinduction o₂; intro f_eq, 
    any_goals { refl }, any_goals { hinduction (nat.encode f_eq) },
  end,  
  exact @inj_to_Set_is_set ring_ops (to_Set ℕ) f inj_f 
end  

@[hott]
def ring_ops_Set : Set.{0} := Set.mk ring_ops ring_ops_is_set

@[hott]
inductive ring_rels : Type 0 
| add_assoc : ring_rels 
| zero_add : ring_rels
| add_zero : ring_rels
| neg_add : ring_rels
| add_comm : ring_rels
| mul_assoc : ring_rels
| one_mul : ring_rels 
| mul_one : ring_rels
| mul_comm : ring_rels
| right_distrib : ring_rels
| left_distrib : ring_rels

@[hott]
def ring_rels_is_set : is_set ring_rels := 
begin
  let f : ring_rels -> ℕ := 
    begin 
      intro r, hinduction r, exact 0, exact 1, exact 2, exact 3, exact 4,
      exact 5, exact 6, exact 7, exact 8, exact 9, exact 10
    end,
  have inj_f : ∀ r₁ r₂ : ring_rels, f r₁ = f r₂ -> r₁ = r₂, from 
  begin
    intros r₁ r₂, hinduction r₁; hinduction r₂; intro f_eq, 
    any_goals { refl }, any_goals { hinduction (nat.encode f_eq) },
  end,  
  exact @inj_to_Set_is_set ring_rels (to_Set ℕ) f inj_f 
end  

@[hott]
def ring_rels_Set : Set.{0} := Set.mk ring_rels ring_rels_is_set

@[hott, hsimp]
def ring_signature : fo_signature :=
begin
  fapply fo_signature.mk, 
  { exact ring_ops_Set }, 
  { exact ring_rels_Set },
  { intro o, hinduction o, exact fin_Set 2, exact fin_Set 0, exact fin_Set 1, 
    exact fin_Set 2, exact fin_Set 0 },
  { intro r, hinduction r, exact fin_Set 3, exact fin_Set 1, exact fin_Set 1, 
    exact fin_Set 1, exact fin_Set 2, exact fin_Set 3, exact fin_Set 1, exact fin_Set 1, 
    exact fin_Set 2, exact fin_Set 3, exact fin_Set 3 } 
end     

/- To use the standard operation notations we need to define some instances. -/
@[hott]
def ring_add (R : Ω_structure ring_signature) : 
  R.carrier -> R.carrier -> R.carrier :=
begin intros x y, exact R.str.ops ring_ops.add (list_to_fin_Set (x :: y :: [])) end

@[hott, instance]
def ring_Ω_str_has_add (R : Ω_structure ring_signature) : has_add R.carrier :=
  ⟨ring_add R⟩

@[hott, instance]
def ring_Ω_str_has_zero (R : Ω_structure ring_signature) : has_zero R.carrier :=
begin 
  apply has_zero.mk,  
  exact R.str.ops ring_ops.zero (list_to_fin_Set []) 
end

@[hott, instance]
def ring_Ω_str_has_neg (R : Ω_structure ring_signature) : has_neg R.carrier :=
begin 
  apply has_neg.mk, intro x, 
  exact R.str.ops ring_ops.neg (list_to_fin_Set (x :: [])) 
end

@[hott, instance]
def ring_Ω_str_has_mul (R : Ω_structure ring_signature) : has_mul R.carrier :=
begin 
  apply has_mul.mk, intros x y, 
  exact R.str.ops ring_ops.mul (list_to_fin_Set (x :: y :: [])) 
end

@[hott, instance]
def ring_Ω_str_has_one (R : Ω_structure ring_signature) : has_one R.carrier :=
begin 
  apply has_one.mk,  
  exact R.str.ops ring_ops.one (list_to_fin_Set []) 
end

/- We define a predicate on the Ω-structures on sets having the ring signature, using a
   predicate on ring relations. -/
@[hott, instance]
def ring_str_is_inhabited {R : Ω_structure ring_signature} : inhabited R.carrier :=
  ⟨R.str.ops ring_ops.zero (list_to_fin_Set [])⟩

@[hott]
def ring_laws : signature_laws ring_signature :=
begin  
 intros R r, hinduction r, all_goals {hsimp, intro x},
 { exact to_Prop ((x^[0] + x^[1]) + x^[2] = x^[0] + (x^[1] + x^[2])) },  
 { exact to_Prop (0 + x^[0] = x^[0]) },
 { exact to_Prop (x^[0] + 0 = x^[0]) },
 { exact to_Prop ((-(x^[0])) + x^[0] = 0) },
 { exact to_Prop (x^[0] + x^[1] = x^[1] + x^[0]) },
 { exact to_Prop ((x^[0] * x^[1]) * x^[2] = x^[0] * (x^[1] * x^[2])) },
 { exact to_Prop (1 * x^[0] = x^[0]) },
 { exact to_Prop (x^[0] * 1 = x^[0]) },
 { exact to_Prop (x^[0] * x^[1] = x^[1] * x^[0]) },
 { exact to_Prop ((x^[0] + x^[1]) * x^[2] = x^[0] * x^[2] + x^[1] * x^[2]) },
 { exact to_Prop (x^[0] * (x^[1] + x^[2]) = x^[0] * x^[1] + x^[0] * x^[2]) } 
end                       

@[hott]
def CommRing := Ω_str_subtype ring_laws

@[hott]
instance CommRing_to_Set : has_coe CommRing Set :=
  ⟨λ R : CommRing, R.1.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing :=
  has_coe_to_sort.mk (Type _) (λ R : CommRing, R.1.carrier)  

/- We construct an Ω-structure of a ring signature from a `comm_ring` structure. -/
@[hott, instance]
def comm_ring_is_inhabited {R : Set} (α : comm_ring R) : inhabited R.carrier :=
  ⟨α.zero⟩

@[hott]
def ring_structure_on {R : Set} (α : comm_ring R) [inhabited R.carrier] : 
  Ω_structure_on ring_signature R :=
begin
  fapply Ω_structure_on.mk,
  { intro o, hinduction o, all_goals {hsimp, intro x},
    { exact x^[0] + x^[1] },
    { exact 0 },
    { exact -(x^[0]) },
    { exact x^[0] * x^[1] },
    { exact 1 } },
  { intro r, hinduction r, all_goals {hsimp, intro x},
      { exact (to_Prop ((x^[0] + x^[1]) + (x^[2]) = x^[0] + (x^[1] + x^[2]))) },
      { exact to_Prop (0 + x^[0] = x^[0]) },
      { exact to_Prop (x^[0] + 0 = x^[0]) },
      { exact to_Prop ((-(x^[0])) + x^[0] = 0) },
      { exact to_Prop (x^[0] + x^[1] = x^[1] + x^[0]) },
      { exact to_Prop ((x^[0] * x^[1]) * x^[2] = x^[0] * (x^[1] * x^[2])) },
      { exact to_Prop (1 * x^[0] = x^[0]) },
      { exact to_Prop (x^[0] * 1 = x^[0]) },
      { exact to_Prop (x^[0] * x^[1] = x^[1] * x^[0]) },
      { exact to_Prop ((x^[0] + x^[1]) * x^[2] = (x^[0] * x^[2]) + (x^[1] * x^[2])) },
      { exact to_Prop (x^[0] * (x^[1] + x^[2]) = (x^[0] * x^[1]) + (x^[0] * x^[2])) } }
  end 

@[hott]
def comm_ring_to_CommRing {R : Set} (α : comm_ring R) : CommRing :=
begin
  fapply dpair,
  { fapply std_structure.mk, 
    { exact R },
    { exact @ring_structure_on R α (comm_ring_is_inhabited α) } },
  { apply prop_to_prop_resize, apply prod.mk, 
    { intros r, hinduction r, 
      all_goals { hsimp, intro x, fapply pair, 
        { intro p, exact p },
        { intro q, exact q } } }, 
    { intro r, hinduction r, all_goals {hsimp, intro x, apply proof_is_true_Prop},
      { fapply α.add_assoc }, 
      { fapply α.zero_add }, 
      { fapply α.add_zero }, 
      { fapply α.add_left_inv }, 
      { fapply α.add_comm }, 
      { fapply α.mul_assoc }, 
      { fapply α.one_mul }, 
      { fapply α.mul_one }, 
      { fapply α.mul_comm }, 
      { fapply α.right_distrib }, 
      { fapply α.left_distrib } } }
end  

@[hott]
def CommRing_to_comm_ring (R : CommRing) : comm_ring R :=
begin
  fapply comm_ring.mk,
  { apply_instance },
  { intros r s, exact r + s },
  { intros r s t, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2 
                              ring_rels.add_assoc (list_to_fin_Set (r::s::t::[]))) },
  { exact 0 },
  { intro r, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2 
                              ring_rels.zero_add (list_to_fin_Set (r::[]))) },
  { intro r, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2 
                              ring_rels.add_zero (list_to_fin_Set (r::[]))) },
  { intro r, exact -r },
  { intro r, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2 
                              ring_rels.neg_add (list_to_fin_Set (r::[]))) },
  { intros r s, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2 
                              ring_rels.add_comm (list_to_fin_Set (r::s::[]))) },
  { intros r s, exact r * s },
  { intros r s t, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.mul_assoc (list_to_fin_Set (r::s::t::[]))) },
  { exact 1 },
  { intro r, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.one_mul (list_to_fin_Set (r::[]))) },
  { intro r, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.mul_one (list_to_fin_Set (r::[]))) },
  { intros r s t, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.left_distrib (list_to_fin_Set (r::s::t::[]))) },
  { intros r s t, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.right_distrib (list_to_fin_Set (r::s::t::[]))) },
  { intros r s, exact proof_of_true_Prop ((prop_resize_to_prop R.2).2
                              ring_rels.mul_comm (list_to_fin_Set (r::s::[]))) }
end  

/- Subrings are subsets of rings with the induced ring structure. So they can be 
   constructed from the data of a subset and the closedness under operations which we
   collect in a structure. For the construction we need the functoriality and the left 
   exactness of the ring laws. A subring structure can be coerced into a `CommRing`. -/
@[hott]
structure is_Subring (S : CommRing) :=
  (subset : Subset S.1.carrier)
  (ops_closed : ops_closed subset)

@[hott]
def funct_ring_laws : funct_sign_laws ring_laws :=
  sorry

@[hott]
def left_exact_ring_laws : left_exact_sign_laws ring_laws :=
  sorry  

#check funct_ring_laws

@[hott]
def Subring.mk {S : CommRing} (R : is_Subring S) : CommRing :=
  law_str_subset funct_ring_laws left_exact_ring_laws R.subset R.ops_closed

@[hott]
def CommSubring {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P] : CommRing :=
  CommRing.mk (pred_Set P) (comm_subring P)

@[hott]
def CommSubring.to_Subset {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P] : 
  Subset R.carrier :=
{r ∈ R.carrier | P r}    

/- The embedding of the underlying subset of a subring into the underlying set of the ring is a 
   ring homomorphism. -/
@[hott]
def comm_subring_embed_hom {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P]:
  comm_ring_str.H (CommSubring P).str R.str (pred_Set_map (CommSubring.to_Subset P)) :=
begin 
  fapply is_ring_hom.mk, 
  { refl },
  { intros r s, refl },
  { refl },
  { intros r s, refl }
end     

/- Units of a ring as a bundled structure. Since for a given ring element there is at most a 
   unique inverse we can also define a predicate identifying invertible ring elements. -/
@[hott]
structure units (R : CommRing) :=
(val : R)
(inv : R)
(val_inv : val * inv = 1)

namespace units

@[hott] 
instance (R : CommRing) : has_coe (units R) R := ⟨val⟩

end units

open units

@[hott]
def unique_mul_inv {R : CommRing.{u}} (r : R) : is_prop (Σ (u : units R), r = u) :=
begin 
  fapply is_prop.mk, intros x y, fapply sigma_eq, 
  { hinduction x.1, hinduction y.1, 
    have H : val = val_1, from
    begin
      have p : x.1.val = val, from ap units.val _h, 
      rwr <- p, change ↑(x.1) = val_1, rwr <- x.2, 
      have q : y.1.val = val_1, from ap units.val _h_1, 
      rwr <- q, change r = ↑(y.1), rwr <- y.2
    end, 
    have H' : inv = inv_1, from 
      calc inv = inv * 1 : (comm_ring.mul_one inv)⁻¹
           ... = inv * (val_1 * inv_1) : by rwr val_inv_1
           ... = inv * (val * inv_1) : by rwr H
           ... = (inv * val) * inv_1 : (comm_ring.mul_assoc inv val inv_1)⁻¹
           ... = (val * inv) * inv_1 : ap (λ r : R, r * inv_1) (comm_ring.mul_comm inv val)
           ... = 1 * inv_1 : by rwr val_inv
           ... = inv_1 : comm_ring.one_mul inv_1, 
    fapply apd001 units.mk, 
    { exact H },
    { exact H' },
    { apply pathover_of_tr_eq, exact is_set.elim _ _ } },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end

@[hott]
def is_unit {R : CommRing} (r : R) : trunctype -1 :=
  trunctype.mk (Σ (u : units R), r = u) (unique_mul_inv r)

@[hott]
class local_ring (R : CommRing) :=
  (nontrivial : ¬ (0 = 1))
  (is_local : ∀ r : R, (is_unit r) or (is_unit (1 - r)))

/- For the constructions of limits and colimits of rings over diagrams in arbitrary universe 
   levels we need to lift the universe level of commutative rings. -/
@[hott]
def CommRing_ulift : CommRing.{u} -> CommRing.{(max u' u)} :=
begin
  intro R, fapply CommRing.mk,
  { exact trunctype_ulift R.carrier },
  { let α := comm_ring_to_ops R.str,
    fapply comm_ring_mk, 
    { fapply comm_ring_ops.mk, 
      { intros r s, exact ulift.up (α.add (ulift.down r) (ulift.down s)) }, --add
      { exact ulift.up α.zero }, --zero
      { intro r, exact ulift.up (α.neg (ulift.down r)) }, --neg
      { intros r s, exact ulift.up (α.mul (ulift.down r) (ulift.down s)) }, --mul
      { exact ulift.up α.one }, }, --one
    { fapply comm_ring_laws.mk, 
      { intros r s t, hsimp, rwr R.str.add_assoc }, --add_assoc
      { intro r, hsimp, rwr R.str.zero_add, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --zero_add
      { intro r, hsimp, rwr R.str.add_zero, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --add_zero
      { intro r, hsimp, rwr R.str.add_left_inv }, --neg_add
      { intros r s, hsimp, rwr R.str.add_comm }, --add_comm
      { intros r s t, hsimp, rwr R.str.mul_assoc }, --mul_assoc
      { intro r, hsimp, rwr R.str.one_mul, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --one_mul
      { intro r, hsimp, rwr R.str.mul_one, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --mul_one
      { intros r s, hsimp, rwr R.str.mul_comm }, --mul_comm
      { intros r s t, hsimp, rwr R.str.left_distrib }, --left_distrib
      { intros r s t, hsimp, rwr R.str.right_distrib } } } --right_distrib
end    

@[hott]
def ring_ulift_functor : CommRing.{u} ⥤ CommRing.{(max u' u)} :=
begin
  fapply categories.functor.mk,
  { exact CommRing_ulift },
  { intros R S f, fapply dpair, 
    { intro r, exact ulift.up (f.1 r.down) },
    { apply prop_to_prop_resize, fapply is_ring_hom.mk, 
      { apply hott.eq.inverse, apply down_eq_up, 
        apply ((prop_resize_to_prop f.2).map_one)⁻¹ }, 
      { intros r s, apply ap ulift.up, 
        apply ((prop_resize_to_prop f.2).map_mul) }, 
      { apply hott.eq.inverse, apply down_eq_up, 
        apply ((prop_resize_to_prop f.2).map_zero)⁻¹ }, 
      { intros r s, apply ap ulift.up, 
        apply ((prop_resize_to_prop f.2).map_add) } } },
  { intro R, apply hom_eq_C_std, apply eq_of_homotopy, 
    intro r, apply hott.eq.inverse, apply down_eq_up, refl }, 
  { intros R S T f g, apply hom_eq_C_std, apply eq_of_homotopy, 
    intro r, apply hott.eq.inverse, apply down_eq_up, refl } 
end  

end algebra

end hott