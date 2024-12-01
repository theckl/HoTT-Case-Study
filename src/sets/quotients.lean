import hott.init hott.types.trunc prop_logic hott.types.prod hott.hit.quotient 
       hott.algebra.relation sets.basic

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv hott.prod hott.quotient hott.sigma hott.relation

namespace set

/- The quotient of a set by a mere relation is made into a set by truncation. -/
@[hott]  --[GEVE]
def set_quotient {A : Set} (R : A -> A -> Prop) : Set :=
  to_Set (trunc 0 (quotient (λ a b : A, R a b)))

@[hott] 
def set_class_of {A : Set} (R : A → A → Prop) (a : A) : set_quotient R :=  
  tr (class_of (λ a b : A, R a b) a) 

@[hott]
def eq_of_setrel {A : Set} (R : A → A → Prop) ⦃a a' : A⦄ (H : R a a') :
  set_class_of R a = set_class_of R a' :=
ap tr (eq_of_rel (λ a b : A, R a b) H)  

@[hott]  --[GEVE]
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

@[hott]
def class_eq_eqv_rel {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] : 
  Π a b : A, set_class_of R a = set_class_of R b ≃ R a b :=
begin
  intros a b, fapply prop_iff_equiv, fapply prod.mk,
  { intro p, 
    exact (quot_eq_eqv_quot_rel R (set_class_of R a) (set_class_of R b)).to_fun p },
  { intro H, exact eq_of_setrel R H }
end

/- We characterize set quotient using the (higher) constructors and the induction principle. -/
@[hott]  --[GEVE]
structure is_cons_quotient {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] (Q : Set) :=
(proj : A -> Q)
(gen : Π (q : Q), trunc -1 (Σ (a : A), proj a = q))
(eq : Π (a₁ a₂ : A), proj a₁ = proj a₂ <-> R a₁ a₂)

@[hott]
structure cons_set_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] :=
  (carrier : Set)
  (is_quot : is_cons_quotient R carrier)

/- Some examples where the criterion is easy to check:

   Relations induced by equality -/
@[hott]  
def eq_rel (A : Set) : A -> A -> Prop :=
  λ a b, trunctype.mk (a = b) (is_trunc_eq -1 a b) 

@[hott, instance]
def eq_is_equiv_rel {A : Set} : is_equivalence (λ a b, eq_rel A a b) :=
  is_equivalence.mk (λ a, @idp _ a) (λ a b p, p⁻¹) (λ a b c p q, p ⬝ q)

@[hott] --[GEVE]
def id_is_cons_quotient_eq (A : Set) : is_cons_quotient (eq_rel A) A :=
  is_cons_quotient.mk id (λ a, tr ⟨a,idp⟩) (λ a₁ a₂, prod.mk id id)

/- Relations induced by maps -/
@[hott]
def map_rel {A B : Set} (q : A -> B) : A -> A -> Prop :=
  λ a b, trunctype.mk (q a = q b) (is_trunc_eq -1 (q a) (q b))

@[hott, instance]
def map_rel_is_equiv_rel {A B : Set} (q : A -> B) : is_equivalence (λ a b, map_rel q a b) := 
  is_equivalence.mk (λ a, @idp _ (q a)) (λ a b p, p⁻¹) (λ a b c p q, p ⬝ q)

@[hott]  --[GEVE]
def image_is_cons_quotient_map_rel {A B : Set} (q : A -> B) : 
  is_cons_quotient (map_rel q) (image_Set q) :=
begin
  fapply is_cons_quotient.mk, 
  { exact λ a, ⟨(q a), tr ⟨a, idp⟩⟩ },
  { intro b, hinduction b with b im, hinduction im with fib, hinduction fib with a eq,
    fapply tr, fapply dpair, exact a, fapply sigma.sigma_eq, exact eq,
    apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { intros a₁ a₂, fapply prod.mk,
    { intro eq, exact eq..1 },
    { intro eq, fapply sigma.sigma_eq, exact eq, 
      apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

/- The total relation -/
@[hott]  
def total_rel (A : Set) : A -> A -> Prop :=
  λ a b, trunctype.mk One One_is_prop 

@[hott, instance]
def total_rel_is_equiv_rel {A : Set} : is_equivalence (λ a b, total_rel A a b) := 
  is_equivalence.mk (λ a, One.star) (λ a b s, s) (λ a b c s t, s)

@[hott]  --[GEVE]
def One_is_cons_quotient_total_rel (A : Set) (H : is_non_empty_Set A) : 
  is_cons_quotient (total_rel A) One_Set :=
begin
  fapply is_cons_quotient.mk, 
  { intro a, exact One.star },
  { intro q, hinduction H with a, apply tr, fapply dpair, exact a, 
    exact @is_prop.elim _ One_is_prop _ _ },
  { intros a₁ a₂, fapply prod.mk, intro p, exact One.star, intro s, exact idp }
end

/- The general construction of the set quotient of an equivalence relation can be 
   characterized by constructors. -/
@[hott]  --[GEVE]
def set_quotient_is_cons_quotient {A : Set} (R : A -> A -> Prop) 
  [is_equivalence (λ a b : A, R a b)] : is_cons_quotient R (set_quotient R) :=
begin
  fapply is_cons_quotient.mk,
  { intro a, exact set_class_of R a },
  { intro q, apply @set_quotient.rec _ R (λ q, trunc -1 (Σ (a : ↥A), set_class_of R a = q)) 
                                      _ (λ a, tr ⟨a, idp⟩), 
    intros a a' H, apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { intros a₁ a₂, fapply prod.mk,
    { intro p, exact class_eq_eqv_rel R a₁ a₂ p },
    { intro H, exact (class_eq_eqv_rel R a₁ a₂)⁻¹ᶠ H } }
end

/- The inductive characterisation of set quotients, making them into initial objects -/
@[hott] 
structure is_ind_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) :=
(proj : A -> Q)
(rel_eq : Π (a b : A), R a b -> proj a = proj b)
(map : Π (P : Set) (f : A -> P), (Π (a b : A), R a b -> f a = f b) -> 
                                                          Σ (g : Q -> P), f = g ∘ proj)
(unique :  Π (P : Set) (f : A -> P) (H : Π (a b : A), R a b -> f a = f b) (g₁ g₂ : Q -> P),
              g₁ ∘ proj = g₂ ∘ proj -> g₁ = g₂)

@[hott, instance] 
def well_defined_element {A : Set} {R : A → A → Prop} [is_equivalence (λ a b : A, R a b)] 
  {Q : Set} (is_quot : is_cons_quotient R Q) {P : Set} (f : A -> P) 
  (rel_eq : Π (a b : A), R a b -> f a = f b) : Π q : Q, is_prop (Σ p : P, 
  trunc -1 (Σ (fib : Σ (a : A), is_quot.proj a = q), (f fib.1 = p))) :=
begin
  intro q, fapply is_prop.mk, intros fib_P₁ fib_P₂, fapply sigma.sigma_eq,
  { hinduction fib_P₁.2 with sec₁ fib₁, hinduction fib_P₂.2 with sec₂ fib₂,
    rwr <- fib₁.2, rwr <- fib₂.2, apply rel_eq, apply (is_quot.eq _ _).1,
    exact fib₁.1.2 ⬝ fib₂.1.2⁻¹ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end 

@[hott] 
def well_defined_map_from_quotient {A : Set} {R : A → A → Prop} 
  [is_equivalence (λ a b : A, R a b)] {Q : Set} (is_quot : is_cons_quotient R Q)
  {P : Set} (f : A -> P) (rel_eq : Π (a b : A), R a b -> f a = f b) : Π q : Q, 
  Σ p : P, trunc -1 (Σ (fib : Σ (a : A), is_quot.proj a = q), (f fib.1 = p)) :=
begin
  intro q, fapply λ H, trunc.elim H (is_quot.gen q),
  { intro fib, fapply dpair, exact f fib.1, exact tr ⟨fib, idp⟩ },
  { exact well_defined_element is_quot f rel_eq q }
end

@[hott]  --[GEVE]
def cons_to_ind_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_cons_quotient R Q -> is_ind_quotient R Q :=
begin
  intro is_quot, fapply is_ind_quotient.mk,
  { exact is_quot.proj },
  { exact λ a b, (is_quot.eq a b).2},
  { intros P f rel_eq, fapply dpair,
    { intro q, exact (well_defined_map_from_quotient is_quot f rel_eq q).1 },
    { apply eq_of_homotopy, intro a,
      hinduction (well_defined_map_from_quotient is_quot f rel_eq (is_quot.proj a)).2
                 with sec fib,
      change _ = (well_defined_map_from_quotient is_quot f rel_eq _).1, rwr <- fib.2,
      apply rel_eq, apply (is_quot.eq _ _).1, exact fib.1.2⁻¹ } },
  { intros P f rel_eq g₁ g₂ g_eq, apply eq_of_homotopy, intro q, 
    hinduction is_quot.gen q with sec fib, rwr <- fib.2, 
    change (g₁ ∘ is_quot.proj) _ = (g₂ ∘ is_quot.proj) _, exact ap10 g_eq fib.1 }
end

@[hott]  --[GEVE]
def ind_to_cons_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_ind_quotient R Q -> is_cons_quotient R Q :=
begin 
  intro is_quot, 
  have map_Q : Σ (g : Q -> set_quotient R), 
                    (set_quotient_is_cons_quotient R).proj = g ∘ is_quot.proj, from 
    sorry,
  have map : Σ (h : set_quotient R -> Q), 
                    is_quot.proj = h ∘ (set_quotient_is_cons_quotient R).proj, from 
    sorry, 
  have map_id_Q : map.1 ∘ map_Q.1 = id, from sorry, 
  have map_id : map_Q.1 ∘ map.1 = id, from sorry,
  fapply is_cons_quotient.mk,
  { exact is_quot.proj },
  { intro q, hinduction (set_quotient_is_cons_quotient R).gen (map_Q.1 q) with sec fib,
    apply tr, fapply dpair, exact fib.1, rwr ap10 map.2 fib.1, 
    have p : (set_quotient_is_cons_quotient R).proj fib.1 = map_Q.fst q, from fib.2,
    change map.1 _ = _, rwr p, exact ap10 map_id_Q q },
  { intros a₁ a₂, fapply prod.mk, 
    { intro p, fapply ((set_quotient_is_cons_quotient R).eq a₁ a₂).1, 
      have q : (set_quotient_is_cons_quotient R).proj = map_Q.1 ∘ is_quot.proj, from map_Q.2,
      rwr q, exact ap map_Q.1 p }, 
    { intro rel, 
      have q : is_quot.proj = map.1 ∘ (set_quotient_is_cons_quotient R).proj, from map.2,
      rwr q, exact ap map.1 (((set_quotient_is_cons_quotient R).eq a₁ a₂).2 rel) } }
end

/- Constructively characterized set quotient are uniquely equal. -/

end set

end hott