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

@[hott]
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
@[hott]
def ring_laws : signature_laws ring_signature :=
begin  
 intros R r args, hinduction r,
 { exact to_Prop (∀ x y z : R.carrier, (ring_add R x y) + z = x + (y + z)) },  
 { exact to_Prop (∀ x : R.carrier, 0 + x = x) },
 { exact to_Prop (∀ x : R.carrier, x + 0 = x) },
 { exact to_Prop (∀ x : R.carrier, (-x) + x = 0) },
 { exact to_Prop (∀ x y: R.carrier, x + y = y + x) },
 { exact to_Prop (∀ x y z : R.carrier, (x * y) * z = x * (y * z)) },
 { exact to_Prop (∀ x : R.carrier, 1 * x = x) },
 { exact to_Prop (∀ x : R.carrier, x * 1 = x) },
 { exact to_Prop (∀ x y: R.carrier, x * y = y * x) },
 { exact to_Prop (∀ x y z : R.carrier, (x + y) * z = x * z + y * z) },
 { exact to_Prop ((Π args, (R.str.rels ring_rels.left_distrib args).carrier) <-> 
                        (∀ x y z : R.carrier, x * (y + z) = x * y + x * z)) and 
         is_true (to_Prop (∀ x y z : R.carrier, x * (y + z) = x * y + x * z)) } 
end                       

@[hott]
def ring_Ω_str_pred : Ω_structure_pred ring_signature :=
  assume R, to_Prop (∀ r : ring_rels, ring_rels_pred R r)

@[hott]
def CommRing := @Ω_str_subtype ring_signature ring_Ω_str_pred

@[hott]
instance CommRing_to_Set : has_coe CommRing Set :=
  ⟨λ R : CommRing, R.1.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing :=
  has_coe_to_sort.mk (Type _) (λ R : CommRing, R.1.carrier)  

/- We construct an Ω-structure of a ring signature from a `comm_ring` structure. -/
@[hott, instance]
def ring_is_inhabited {R : Set} [α : comm_ring R] : inhabited ↥R :=
  ⟨0⟩

@[hott]
def ring_structure_on {R : Set} (α : comm_ring R) : Ω_structure_on ring_signature R :=
  begin
    fapply Ω_structure_on.mk,
    { intros o x, hinduction o, 
      { let vals := @fin_Set_to_list _ 2 x, let r := head vals, let s := head (tail vals),
        exact r + s },
      { exact 0 },
      { let val := @fin_Set_to_list _ 1 x, let r := head val, exact -r },
      { let vals := @fin_Set_to_list _ 2 x, let r := head vals, let s := head (tail vals),
        exact r * s },
      { exact 1 } },
    { intros r x, hinduction r, 
      { let vals := @fin_Set_to_list _ 3 x, let r := head vals, let s := head (tail vals),
        let t := head (tail (tail vals)), exact to_Prop ((r + s) + t = r + (s + t)) },
      { let vals := @fin_Set_to_list _ 1 x, let r := head vals, exact to_Prop (0 + r = r) },
      { let vals := @fin_Set_to_list _ 1 x, let r := head vals, exact to_Prop (r + 0 = r) },
      { let vals := @fin_Set_to_list _ 1 x, let r := head vals, exact to_Prop ((-r) + r = 0) },
      { let vals := @fin_Set_to_list _ 2 x, let r := head vals, let s := head (tail vals),
        exact to_Prop (r + s = s + r) },
      { let vals := @fin_Set_to_list _ 3 x, let r := head vals, let s := head (tail vals),
        let t := head (tail (tail vals)), exact to_Prop ((r * s) * t = r * (s * t)) },
      { let vals := @fin_Set_to_list _ 1 x, let r := head vals, exact to_Prop (1 * r = r) },
      { let vals := @fin_Set_to_list _ 1 x, let r := head vals, exact to_Prop (r * 1 = r) },
      { let vals := @fin_Set_to_list _ 2 x, let r := head vals, let s := head (tail vals),
        exact to_Prop (r * s = s * r) },
      { let vals := @fin_Set_to_list _ 3 x, let r := head vals, let s := head (tail vals),
        let t := head (tail (tail vals)), exact to_Prop ((r + s) * t = (r * t) + (s * t)) },
      { let vals := @fin_Set_to_list _ 3 x, let r := head vals, let s := head (tail vals),
        let t := head (tail (tail vals)), exact to_Prop (r * (s + t) = (r * s) + (r * t)) } }
  end 

@[hott]
def comm_ring_to_CommRing {R : Set} (α : comm_ring R) : CommRing :=
begin
  fapply dpair,
  { fapply std_structure.mk, 
    { exact R },
    { exact ring_structure_on α } },
  { intro r, hinduction r, 
    { fapply pair, 
      { fapply pair,
        { intros p x y z, exact p (list_to_fin_Set (x::y::z::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 3 args, let x := head vals, 
          let y := head (tail vals), let z := head (tail (tail vals)), exact q x y z } },
      { exact proof_is_true_Prop α.add_assoc } },    
    { fapply pair,
      { fapply pair,
        { intros p x, exact p (list_to_fin_Set (x::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 1 args, let x := head vals, 
          exact q x } },
      { exact proof_is_true_Prop α.zero_add } },    
    { fapply pair,
      { fapply pair,
        { intros p x, exact p (list_to_fin_Set (x::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 1 args, let x := head vals, 
          exact q x } },
      { exact proof_is_true_Prop α.add_zero } },    
    { fapply pair,
      { fapply pair,
        { intros p x, exact p (list_to_fin_Set (x::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 1 args, let x := head vals, 
          exact q x } },
      { exact proof_is_true_Prop α.add_left_inv } },   
    { fapply pair,
      { fapply pair,
        { intros p x y, exact p (list_to_fin_Set (x::y::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 2 args, let x := head vals, 
          let y := head (tail vals), exact q x y } },
      { exact proof_is_true_Prop α.add_comm } },
    { fapply pair,
      { fapply pair,
        { intros p x y z, exact p (list_to_fin_Set (x::y::z::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 3 args, let x := head vals, 
          let y := head (tail vals), let z := head (tail (tail vals)), exact q x y z } },
      { exact proof_is_true_Prop α.mul_assoc } },    
    { fapply pair,
      { fapply pair,
        { intros p x, exact p (list_to_fin_Set (x::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 1 args, let x := head vals, 
          exact q x }},
      { exact proof_is_true_Prop α.one_mul } },
    { fapply pair,
      { fapply pair,
        { intros p x, exact p (list_to_fin_Set (x::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 1 args, let x := head vals, 
          exact q x } },
      { exact proof_is_true_Prop α.mul_one } },    
    { fapply pair,
      { fapply pair,
        { intros p x y, exact p (list_to_fin_Set (x::y::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 2 args, let x := head vals, 
          let y := head (tail vals), exact q x y } },
      { exact proof_is_true_Prop α.mul_comm } },    
    { fapply pair,
      { fapply pair,
        { intros p x y z, exact p (list_to_fin_Set (x::y::z::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 3 args, let x := head vals, 
          let y := head (tail vals), let z := head (tail (tail vals)), exact q x y z } },
      { exact proof_is_true_Prop α.right_distrib } },    
    { fapply pair,
      { fapply pair,
        { intros p x y z, exact p (list_to_fin_Set (x::y::z::[])) },
        { intros q args, let vals := @fin_Set_to_list _ 3 args, let x := head vals, 
          let y := head (tail vals), let z := head (tail (tail vals)), exact q x y z } } },
      { exact proof_is_true_Prop α.left_distrib } }
end  

@[hott]
def CommRing_to_comm_ring (R : CommRing) : comm_ring R :=
begin
  fapply comm_ring.mk,
  { apply_instance },
  { intros r s, exact r + s },
  { exact proof_of_true_Prop (R.2 ring_rels.add_assoc).2 },
  { exact 0 },
  { exact proof_of_true_Prop (R.2 ring_rels.zero_add).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.add_zero).2 },
  { intro r, exact -r },
  { exact proof_of_true_Prop (R.2 ring_rels.neg_add).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.add_comm).2 },
  { intros r s, exact r * s },
  { exact proof_of_true_Prop (R.2 ring_rels.mul_assoc).2 },
  { exact 1 },
  { exact proof_of_true_Prop (R.2 ring_rels.one_mul).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.mul_one).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.left_distrib).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.right_distrib).2 },
  { exact proof_of_true_Prop (R.2 ring_rels.mul_comm).2 }
end  

/- A criterion to decide whether a subset of a commutative ring given by a predicate is a
   commutative (sub)ring : The ring operation are closed under the predicate. -/ 
@[hott]
class ring_pred_closed {R : CommRing} (P : Subset R.1.carrier) :=
  (add : ∀ r s : R, P r -> P s -> P (r + s)) 
  (zero : P 0) 
  (neg : ∀ r : R, P r -> P (-r))
  (mul : ∀ r s : R, P r -> P s -> P (r * s)) 
  (one : P 1)

@[hott]   
def comm_subring {R : CommRing} (P : Subset R.1.carrier) [ring_pred_closed P] : 
  comm_ring ↥P :=
begin  
  fapply @comm_ring_mk (pred_Set P),
  { fapply comm_ring_ops.mk, 
    { intros r s, exact ⟨r.1 + s.1, ring_pred_closed.add r.1 s.1 r.2 s.2⟩ }, --add
    { exact ⟨0, ring_pred_closed.zero P⟩ }, --zero
    { intro r, exact ⟨-r.1, ring_pred_closed.neg r.1 r.2⟩ }, --neg
    { intros r s, exact ⟨r.1 * s.1, ring_pred_closed.mul r.1 s.1 r.2 s.2⟩ }, --mul
    { exact ⟨1, ring_pred_closed.one P⟩ } }, --one
  { fapply comm_ring_laws.mk, 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.add_assoc r.1 s.1 t.1 }, --add_assoc 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.zero_add r.1 }, --zero_add
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_zero r.1 }, --add_zero 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_left_inv r.1 }, --add_left_inv 
    { intros r s, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_comm r.1 s.1 },  --add_comm 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.mul_assoc r.1 s.1 t.1 }, --mul_assoc
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.one_mul r.1 }, --one_mul 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.mul_one r.1 }, --mul_one 
    { intros r s, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.mul_comm r.1 s.1 }, --mul_comm
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.left_distrib r.1 s.1 t.1 }, --left_distrib 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.right_distrib r.1 s.1 t.1 }, } --right_distrib
end  

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