import hott.init hott.types.trunc prop_logic hott.types.prod hott.hit.quotient 
       hott.algebra.relation sets.basic

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv hott.prod hott.quotient hott.sigma hott.relation

namespace set

/- The quotient of a set by a mere relation is made into a set by truncation. -/
@[hott]
def set_quotient {A : Set} (R : A -> A -> Prop) : Set :=
  to_Set (trunc 0 (quotient (λ a b : A, R a b)))

@[hott] 
def set_class_of {A : Set} (R : A → A → Prop) (a : A) : set_quotient R :=  
  tr (class_of (λ a b : A, R a b) a) 

@[hott]
def eq_of_setrel {A : Set} (R : A → A → Prop) ⦃a a' : A⦄ (H : R a a') :
  set_class_of R a = set_class_of R a' :=
ap tr (eq_of_rel (λ a b : A, R a b) H)  

@[hott]
def set_quotient.rec {A : Set} (R : A → A → Prop) {P : set_quotient R -> Type _} 
  [∀ x : set_quotient R, is_set (P x)] (Pc : Π a : A, P (set_class_of R a))
  (Pp : Π ⦃ a a' : A ⦄ (H : R a a'), Pc a =[eq_of_setrel R H; λ x, P x] Pc a') 
  (x : set_quotient R) : P x :=
begin 
  let P' := λ x, P x, 
  change P' x, apply trunc.rec, 
  let P'' := λ a, P' (tr a), 
  intro a, change P'' a, fapply quotient.rec,
  { intro a, exact Pc a },
  { intros a a' H, exact pathover_of_pathover_ap P' tr (Pp H) } 
end  

@[hott]
def set_quotient.prec {A : Set} (R : A → A → Prop) {P : set_quotient R -> Type _} 
  [∀ x : set_quotient R, is_prop (P x)] (Pc : Π a : A, P (set_class_of R a)) 
  (x : set_quotient R) : P x :=
begin 
  fapply set_quotient.rec, 
  { exact Pc }, 
  { intros a a' H, apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end 

@[hott]
def set_quotient.prec2 {A : Set} (R : A → A → Prop) 
  {P : set_quotient R -> set_quotient R -> Type _} [∀ x y : set_quotient R, is_prop (P x y)] 
  (Pc : Π a b : A, P (set_class_of R a) (set_class_of R b)) (x y : set_quotient R) : P x y :=
begin 
  fapply set_quotient.prec, 
  { intro b, revert x, fapply set_quotient.prec, 
    intro a, exact Pc a b }
end 

@[hott]
def set_quotient.prec3 {A : Set} (R : A → A → Prop) 
  {P : set_quotient R -> set_quotient R -> set_quotient R -> Type _} 
  [∀ x y z : set_quotient R, is_prop (P x y z)] 
  (Pc : Π a b c : A, P (set_class_of R a) (set_class_of R b) (set_class_of R c)) 
  (x y z : set_quotient R) : P x y z :=
begin 
  fapply set_quotient.prec, 
  { intro c, revert y, fapply set_quotient.prec, 
    intro b, revert x, fapply set_quotient.prec, 
    intro a, exact Pc a b c }
end 

@[hott]
def set_quotient.elim {A : Set} (R : A → A → Prop) {P : Type _} [Hs : is_set P] (Pc : A -> P)
  (Pp : Π ⦃ a a' : A ⦄ (H : R a a'), Pc a = Pc a') 
  (x : set_quotient R) : P :=
begin
  let P' := λ x : set_quotient R, P, change P' x, 
  fapply set_quotient.rec R, 
  { intro a, exact Pc a },
  { intros a a' H, change Pc a =[eq_of_setrel R H; λ (x : ↥(set_quotient R)), P] Pc a', 
    apply pathover_of_eq, exact Pp H },
  { intro x, exact Hs }  
end  

@[hott]
def set_class_of_is_surj {A : Set} (R : A → A → Prop) :
  is_set_surjective (set_class_of R) :=
begin 
  fapply set_quotient.rec, 
  { intro a, exact tr ⟨a, idp⟩ },
  { intros a a' H, exact pathover_prop_eq _ _ _ _ } 
end

/- These induction principles should occur in [hit.quotient]. I can't see how to prove the
   equalities of equalities needed for double induction if `P a b` is not a set, but at the
   moment the assumption holds in the applications. -/
@[hott]
def set_quotient.rec2 {A : Set} (R : A → A → Prop) 
  {P : set_quotient R -> set_quotient R -> Type _} 
  [HS : ∀ x y : set_quotient R, is_set (P x y)] 
  (Pc : Π a b : A, P (set_class_of R a) (set_class_of R b))
  (Ppl : Π ⦃ a a' : A ⦄ (b : A) (H : R a a'), 
         Pc a b =[eq_of_setrel R H; λ x, P x (set_class_of R b)] Pc a' b) 
  (Ppr : Π (a : A) ⦃ b b' : A ⦄ (H : R b b'), 
         Pc a b =[eq_of_setrel R H; λ y, P (set_class_of R a) y] Pc a b')        
  (x y : set_quotient R) : P x y :=
begin
  fapply @set_quotient.rec A R (λ x : set_quotient R, Π (y : set_quotient R), P x y),
  { intro a,
    fapply @set_quotient.rec A R (λ y : set_quotient R, P (set_class_of R a) y),
    { intro b, exact Pc a b },
    { intros b b' Hb, exact Ppr a Hb } },
  { intros a a' Ha, apply dep_eq_of_homotopy, 
    fapply set_quotient.rec, 
    { intro b, exact Ppl b Ha },
    { intros b b' Hb, apply pathover_of_tr_eq, 
      apply @dep_set_eq_eq _ (λ x : set_quotient R, P x (set_class_of R b')) 
            (set_class_of R a) (set_class_of R a') 
            (HS (set_class_of R a') (set_class_of R b')) } } 
end 

@[hott]
def set_quotient.elim2 {A : Set} (R : A → A → Prop) {P : Type _} 
  [Hs : is_set P] (Pc : A -> A -> P) 
  (Ppl : Π ⦃ a a' : A ⦄ (b : A) (H : R a a'), Pc a b = Pc a' b) 
  (Ppr : Π (a : A) ⦃ b b' : A ⦄ (H : R b b'), Pc a b = Pc a b')       
  (x y : set_quotient R) : P :=
begin
  fapply @set_quotient.rec2 A R (λ x y : set_quotient R, P),
  { intros a b, exact Pc a b },
  { intros a a' b Ha, change Pc a b =[eq_of_setrel R Ha; λ (x : set_quotient R), P] Pc a' b,
    apply pathover_of_eq, exact Ppl b Ha },
  { intros a b b' Hb, change Pc a b =[eq_of_setrel R Hb; λ (x : set_quotient R), P] Pc a b',
    apply pathover_of_eq, exact Ppr a Hb },
  { exact x },
  { exact y }
end  

/- Equality in the set-quotient of a set by a mere equivalence relation is equivalent to the 
   relation, extended to the set-quotient. This is [HoTT-Book, Lem.10.1.8] (which actually
   states the equivalence `class_of a = class_of b ≃ R a b`, a special case).

   This can be used to deduce equalities of quotient elements from relations between set 
   elements. 
   
   We start with the extension of the relation to the set-quotient. -/
@[hott, reducible]
def equiv_rel_to_set_quotient_rel {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : 
  (set_quotient R) -> (set_quotient R) -> Prop :=
begin
  let R' := λ a b : A, (R a b).carrier,
  fapply @set_quotient.rec2 A R, 
  { exact R },
  { intros a a' b H, apply pathover_of_eq, apply prop_iff_eq, 
    { intro H', exact rel_trans R' (rel_symm R' H) H' },
    { intro H', exact rel_trans R' H H' } },
  { intros a a' b H, apply pathover_of_eq, apply prop_iff_eq, 
    { intro H', exact rel_trans R' H' H },
    { intro H', exact rel_trans R' H' (rel_symm R' H) } } 
end  

/- Now we can show the equivalence on the extended relation. The quasi-isomorphism 
   needs reflexivity of the relation, the inverse is constructed by double induction. -/
@[hott, reducible]
def quot_rel_to_setquot_eq {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : Π x y : set_quotient R,
  (equiv_rel_to_set_quotient_rel R x y) -> (x = y) :=
begin
  let R' := λ a b : A, (R a b).carrier,
  let HP := λ (a b : A), @is_prop_map 
            (equiv_rel_to_set_quotient_rel R (set_class_of R a) (set_class_of R b)) 
            ((set_class_of R a) = (set_class_of R b)) _,
  intros x y,  
  fapply @set_quotient.rec2 A R 
         (λ x y : set_quotient R, (equiv_rel_to_set_quotient_rel R x y) -> (x = y)), 
  { intros a b H, exact eq_of_setrel R H },
  { intros a a' b Ha, apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { intros a b b' Hb, apply pathover_of_tr_eq, exact is_prop.elim _ _  },
  { apply is_prop.mk, intros p q, exact is_set.elim _ _ }
end   

@[hott, reducible]
def quot_eq_eqv_quot_rel {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : Π x y : set_quotient R,
  (x = y) ≃ (equiv_rel_to_set_quotient_rel R x y) :=
begin
  let R' := λ a b : A, (R a b).carrier,
  let Rq := equiv_rel_to_set_quotient_rel R,
  have Rq_symm : Π x : set_quotient R, Rq x x, from 
    begin 
      apply @trunc.rec 0 (quotient R') (λ x : set_quotient R, Rq x x), 
      fapply quotient.rec, 
      { intro a, change R' a a, exact rel_refl R' a },
      { intros a a' H, apply pathover_of_tr_eq, exact is_prop.elim _ _ }
    end,
  intros x y, apply prop_iff_equiv, apply iff.intro,
    { intro p, rwr p, exact Rq_symm y },
    { exact quot_rel_to_setquot_eq R x y }  
end  

end set

end hott