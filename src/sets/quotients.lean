import hott.init hott.types.trunc prop_logic hott.types.prod hott.hit.quotient 
       hott.algebra.relation sets.axioms

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc equiv is_equiv hott.prod hott.quotient hott.sigma hott.relation
     subset

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
(gen : Π (q : Q), ∥ (Σ (a : A), proj a = q) ∥)
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
(rel_eq : Π {a b : A}, R a b -> proj a = proj b)
(map : Π {P : Set} (f : A -> P), (Π {a b : A}, R a b -> f a = f b) -> 
                                                          Σ (g : Q -> P), f = g ∘ proj)
(unique :  Π {P : Set} (f : A -> P) (H : Π {a b : A}, R a b -> f a = f b) (g₁ g₂ : Q -> P),
              g₁ ∘ proj = g₂ ∘ proj -> g₁ = g₂)

@[hott, instance] 
def well_defined_element {A : Set} {R : A → A → Prop} [is_equivalence (λ a b : A, R a b)] 
  {Q : Set} (is_quot : is_cons_quotient R Q) {P : Set} (f : A -> P) 
  (rel_eq : Π {a b : A}, R a b -> f a = f b) : Π q : Q, is_prop (Σ p : P, 
  ∥ Σ (fib : Σ (a : A), is_quot.proj a = q), (f fib.1 = p) ∥) :=
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
  {P : Set} (f : A -> P) (rel_eq : Π {a b : A}, R a b -> f a = f b) : Π q : Q, 
  Σ p : P, ∥ Σ (fib : Σ (a : A), is_quot.proj a = q), (f fib.1 = p) ∥ :=
begin
  intro q, fapply λ H, trunc.elim H (is_quot.gen q),
  { intro fib, fapply dpair, exact f fib.1, exact tr ⟨fib, idp⟩ },
  { exact well_defined_element is_quot f @rel_eq q }
end

@[hott]  --[GEVE]
def cons_to_ind_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_cons_quotient R Q -> is_ind_quotient R Q :=
begin
  intro is_quot, fapply is_ind_quotient.mk,
  { exact is_quot.proj },
  { exact λ a b, (is_quot.eq a b).2},
  { intros P f rel_eq, fapply dpair,
    { intro q, exact (well_defined_map_from_quotient is_quot f @rel_eq q).1 },
    { apply eq_of_homotopy, intro a,
      hinduction (well_defined_map_from_quotient is_quot f @rel_eq (is_quot.proj a)).2
                 with sec fib,
      change _ = (well_defined_map_from_quotient is_quot f @rel_eq _).1, rwr <- fib.2,
      apply rel_eq, apply (is_quot.eq _ _).1, exact fib.1.2⁻¹ } },
  { intros P f rel_eq g₁ g₂ g_eq, apply eq_of_homotopy, intro q, 
    hinduction is_quot.gen q with sec fib, rwr <- fib.2, 
    change (g₁ ∘ is_quot.proj) _ = (g₂ ∘ is_quot.proj) _, exact ap10 g_eq fib.1 }
end

@[hott]
def ind_quot_to_quot_equiv {A : Set} {R : A → A → Prop} [is_equivalence (λ a b : A, R a b)] 
  {Q : Set} (is_quot : is_ind_quotient R Q) : Σ (eqv : set_quotient R ≃ Q), 
                    eqv.to_fun ∘ (set_quotient_is_cons_quotient R).proj = is_quot.proj :=
begin
  fapply dpair,
  { fapply equiv.mk,
    { exact ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map 
                          is_quot.proj is_quot.rel_eq).1 },
    { fapply is_equiv.adjointify, 
      { exact (is_quot.map (set_quotient_is_cons_quotient R).proj
                  (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).rel_eq).1 },
      { intro q, change _ = id q, apply λ p, ap10 p q, 
        fapply is_quot.unique is_quot.proj is_quot.rel_eq,
        apply eq_of_homotopy, intro a, 
        change ((cons_to_ind_quotient _ _ _).map _ _).fst 
                               ((is_quot.map _ _).fst (is_quot.proj a)) = is_quot.proj a,
        have p : (is_quot.map (set_quotient_is_cons_quotient R).proj 
                   (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).rel_eq).fst 
                       (is_quot.proj a) = (set_quotient_is_cons_quotient R).proj a, from
          (ap10 (is_quot.map (set_quotient_is_cons_quotient R).proj 
              (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).rel_eq).2 a)⁻¹,
        rwr p },
      { intro q, change _ = id q, apply λ p, ap10 p q, 
        fapply (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).unique 
                      (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).proj 
                      (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).rel_eq,
        apply eq_of_homotopy, intro a, 
        change (is_quot.map _ _).fst 
                 (((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map _ _).fst 
                  ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).proj a)) = 
                  (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).proj a,
        have p : ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map 
                                                       is_quot.proj is_quot.rel_eq).fst 
                  ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).proj a) = 
                                                                      is_quot.proj a, from
          (ap10 ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map 
                   is_quot.proj is_quot.rel_eq).2 a)⁻¹,
        rwr p, apply ap10 (is_quot.map (set_quotient_is_cons_quotient R).proj
                               (cons_to_ind_quotient R (set_quotient R) 
                                      (set_quotient_is_cons_quotient R)).rel_eq).2⁻¹ a } } },
  { exact ((cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map 
                          is_quot.proj is_quot.rel_eq).2 }
end

@[hott]  --[GEVE]
def ind_to_cons_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_ind_quotient R Q -> is_cons_quotient R Q :=
begin 
  intro is_quot, 
  have map_Q : Σ (g : Q -> set_quotient R), 
                    (set_quotient_is_cons_quotient R).proj = g ∘ is_quot.proj, from 
    is_quot.map _ (λ a b, ((set_quotient_is_cons_quotient R).eq a b).2),
  have eq : (set_quotient_is_cons_quotient R).proj = map_Q.1 ∘ is_quot.proj, from map_Q.2,
  have map : Σ (h : set_quotient R -> Q), 
                    is_quot.proj = h ∘ (set_quotient_is_cons_quotient R).proj, from 
    (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).map _ is_quot.rel_eq, 
  have eq' : is_quot.proj = map.1 ∘ (set_quotient_is_cons_quotient R).proj, from map.2,  
  have map_id_Q : map.1 ∘ map_Q.1 = id, from 
  begin
    apply is_quot.unique is_quot.proj is_quot.rel_eq, apply eq_of_homotopy, intro q,
    change map.1 ((map_Q.fst ∘ is_quot.proj) q) = is_quot.proj _, rwr <- ap10 eq q,
    rwr ap10 eq' q
  end, 
  have map_id : map_Q.1 ∘ map.1 = id, from
  begin
    fapply (cons_to_ind_quotient R _ (set_quotient_is_cons_quotient R)).unique, 
    exact (set_quotient_is_cons_quotient R).proj,
    exact λ a b, ((set_quotient_is_cons_quotient R).eq a b).2, 
    apply eq_of_homotopy, intro a,
    change map_Q.1 ((map.fst ∘ (set_quotient_is_cons_quotient R).proj) a) = 
             (set_quotient_is_cons_quotient R).proj _, rwr <- ap10 eq' a, rwr ap10 eq a
  end,
  fapply is_cons_quotient.mk,
  { exact is_quot.proj },
  { intro q, hinduction (set_quotient_is_cons_quotient R).gen (map_Q.1 q) with sec fib,
    apply tr, fapply dpair, exact fib.1, rwr ap10 map.2 fib.1, 
    have p : (set_quotient_is_cons_quotient R).proj fib.1 = map_Q.fst q, from fib.2,
    change map.1 _ = _, rwr p, exact ap10 map_id_Q q },
  { intros a₁ a₂, fapply prod.mk, 
    { intro p, fapply ((set_quotient_is_cons_quotient R).eq a₁ a₂).1, rwr eq, 
      exact ap map_Q.1 p }, 
    { intro rel, rwr eq', 
      exact ap map.1 (((set_quotient_is_cons_quotient R).eq a₁ a₂).2 rel) } }
end

/- Constructively characterized set quotient are uniquely equal. -/
@[hott]
def cons_quotient_Sigma {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] :=
  Σ (carrier : Set), is_cons_quotient R carrier

@[hott]
def cons_quotient_equiv_Sigma {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : cons_set_quotient R ≃ cons_quotient_Sigma R :=
begin 
  fapply equiv.mk,
  { intro is_quot, hinduction is_quot, exact dpair carrier is_quot },
  { fapply is_equiv.adjointify,
    { intro is_quot, exact cons_set_quotient.mk is_quot.1 is_quot.2 },
    { intro quot, hinduction quot, exact idp },
    { intro quot, hinduction quot, exact idp } }
end

@[hott]  --[GEVE]
def cons_quotient_dep_id_sys {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : 
  dep_ppred (set_quotient R) (set_quotient_is_cons_quotient R) :=
begin
  fapply dep_ppred.mk,
  { exact id_ppred (set_quotient R) },
  { intros Q is_quot p, 
    exact (set_quotient_is_cons_quotient R).proj =[p; λ Q : Set, A -> Q] is_quot.proj },
  { exact idpo }
end

@[hott, instance]
def quot_dep_id_sys_is_prop {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] (is_quot : is_cons_quotient R (set_quotient R)) :
  is_prop ((cons_quotient_dep_id_sys R).dep_fam (set_quotient R) is_quot 
           (cons_quotient_dep_id_sys R).ppred_fst.base) :=
begin change is_prop (_ =[idp] _), apply_instance end

@[hott,instance]
def cons_quotient_eq_contr {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)] : 
  is_contr (Σ (is_quot : is_cons_quotient R (set_quotient R)), 
              ((cons_quotient_dep_id_sys R).dep_fam (set_quotient R) is_quot 
                                      (cons_quotient_dep_id_sys R).ppred_fst.base)) :=
begin
  fapply is_contr.mk,
  { exact dpair (set_quotient_is_cons_quotient R) idpo },
  { intro is_quot, hinduction is_quot with is_quot is_quot_eq, fapply sigma.sigma_eq,
    { hinduction is_quot, fapply apd0111' is_cons_quotient.mk,
      { apply @eq_of_pathover_idp _ (λ Q : Set, A -> Q), exact is_quot_eq },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott]
def cons_quotient_eq_set_quotient {A : Set} {R : A → A → Prop} 
  [is_equivalence (λ a b : A, R a b)] (cons_quot_Sigma : Σ (Q : Set), is_cons_quotient R Q) : 
  Σ (p : set_quotient R = cons_quot_Sigma.1), (cons_quotient_dep_id_sys R).dep_fam 
                                                 cons_quot_Sigma.1 cons_quot_Sigma.2 p :=
begin
  fapply dpair,
  { apply car_eq_to_set_eq, apply ua, 
    exact (ind_quot_to_quot_equiv (cons_to_ind_quotient R _ cons_quot_Sigma.2)).1 },
  { change _ =[car_eq_to_set_eq _] _, apply pathover_of_pathover_ap (λ Q : Type _, A -> Q),
    change _ =[set_eq_equiv_car_eq.to_fun (set_eq_equiv_car_eq.to_fun⁻¹ᶠ _)] _,
    rwr set_eq_equiv_car_eq.to_is_equiv.right_inv, 
    apply fn_pathover_equiv_of_eq', rwr equiv_of_eq_ua }
end

@[hott, instance] --[GEVE]
def cons_quotients_sigma_are_canonically_equal {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)]  : is_contr (cons_quotient_Sigma R) :=
begin 
  fapply is_contr.mk,
  { exact dpair (set_quotient R) (set_quotient_is_cons_quotient R) },
  { intro cons_quot_Sigma, 
    exact (struct_id_char_of_contr _ (cons_quotient_dep_id_sys R) (is_contr_tot_peq _) 
            (cons_quotient_eq_contr R) cons_quot_Sigma)⁻¹ᶠ 
            (cons_quotient_eq_set_quotient cons_quot_Sigma) }
end

@[hott, instance] 
def cons_quotients_are_canonically_equal {A : Set} (R : A → A → Prop)  
  [is_equivalence (λ a b : A, R a b)]  : is_contr (cons_set_quotient R) :=
is_trunc_equiv_closed_rev -2 (cons_quotient_equiv_Sigma R)
                             (cons_quotients_sigma_are_canonically_equal R)

@[hott, instance] 
def cons_quotients_are_canonically_equal' {A : Set} (R : A → A → Prop) 
  [is_equivalence (λ a b : A, R a b)]  : is_prop (cons_set_quotient R) :=
@is_trunc_succ (cons_set_quotient R) -2 (cons_quotients_are_canonically_equal R)

/- We also can characterize quotients by a relation `R` by extracting the generators from
   the quotient set, that is, by asserting the (mere) existence of a section. The 
   corresponding universal property makes the quotient into a terminal object. 
   
   However, the statement that the constructive characterisation implies the mere existence of 
   a section is equivalent to the Axiom of Choice. The converse implication only needs 
   induction over truncation if we can use the uniqueness of a constructively characterised 
   set-quotient. -/
@[hott]
structure section_of_quot {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) :=
(sec : Q -> A)
(proj : Π (a : A), Σ (q : Q), R a (sec q))
(unique : Π (q₁ q₂ : Q), R (sec q₁) (sec q₂) -> q₁ = q₂)

@[hott]
def is_sec_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) := ∥ section_of_quot R Q ∥

@[hott]
def cons_to_sec_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_cons_quotient R Q -> is_sec_quotient R Q :=
begin
  intro is_quot, 
  hinduction AC_nonempty Q (λ q, to_Set (Σ (a : A), is_quot.proj a = q)) is_quot.gen 
                                                                           with AC_eq fib, 
  apply tr, fapply section_of_quot.mk,
  { intro q, exact (fib q).1 },
  { intro a, fapply dpair, exact is_quot.proj a, apply (is_quot.eq _ _).1, 
    exact (fib (is_quot.proj a)).2⁻¹ },
  { intros q₁ q₂ rel_eq, exact (fib q₁).2⁻¹ ⬝ (is_quot.eq _ _).2 rel_eq ⬝ (fib q₂).2 }
end

@[hott, reducible]
def sec_to_cons_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_sec_quotient R Q -> cons_set_quotient R :=
begin
  fapply @trunc.elim' -1 (section_of_quot R Q) _ (cons_quotients_are_canonically_equal' R),
  intro sec_quot, fapply cons_set_quotient.mk,
  { exact Q }, 
  { fapply is_cons_quotient.mk,
    { intro a, exact (sec_quot.proj a).1 },
    { intro q, apply tr, fapply dpair, exact sec_quot.sec q, 
      apply eq.inverse, apply sec_quot.unique, exact (sec_quot.proj (sec_quot.sec q)).2 },
    { intros a₁ a₂, fapply prod.mk,
      { intro p, fapply @rel_trans _ (λ a b, R a b) _ _ (sec_quot.sec (sec_quot.proj a₁).1) _,
        { exact (sec_quot.proj a₁).2 },
        { rwr p, apply rel_symm (λ a b, R a b), exact (sec_quot.proj a₂).2 } },
      { intro rel, apply sec_quot.unique, 
        fapply @rel_trans _ (λ a b, R a b) _ _ a₁ _,
        apply rel_symm (λ a b, R a b), exact (sec_quot.proj a₁).2,
        fapply @rel_trans _ (λ a b, R a b) _ _ a₂ _, exact rel, 
        exact (sec_quot.proj a₂).2 } } }
end

@[hott]
structure term_quot {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) :=
(sec : Q -> A)
(map : Π {P : Set} (sP : P -> A), Σ (f : P -> Q), Π (p : P), R (sP p) (sec (f p)))
(unique : Π {P : Set} (f₁ f₂ : P -> Q), (Π (p : P), R (sec (f₁ p)) (sec (f₂ p))) -> f₁ = f₂) 

@[hott]
def is_term_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) := ∥ term_quot R Q ∥

@[hott]
def sec_to_term_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_sec_quotient R Q -> is_term_quotient R Q :=
begin
  intro is_quot, hinduction is_quot with sec_quot, apply tr, fapply term_quot.mk,
  { exact sec_quot.sec },
  { intros P sP, fapply dpair, 
    { intro p, exact (sec_quot.proj (sP p)).1 },
    { intro p, exact (sec_quot.proj (sP p)).2 } },
  { intros P f₁ f₂ rel, apply eq_of_homotopy, intro p, 
    exact sec_quot.unique _ _ (rel p) }
end

@[hott]
def term_to_sec_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] 
  (Q : Set) : is_term_quotient R Q -> is_sec_quotient R Q :=
begin
  intro is_quot, hinduction is_quot with term_quot, apply tr, fapply section_of_quot.mk,
  { exact term_quot.sec },
  { intro a, let sa : One_Set -> A := @One.rec (λ o, A) a, fapply dpair,
    { exact (term_quot.map sa).1 One.star },
    { exact (term_quot.map sa).2 One.star } },
  { intros q₁ q₂ rel, 
    let f₁ : One_Set -> Q := @One.rec (λ o, Q) q₁, 
    let f₂ : One_Set -> Q := @One.rec (λ o, Q) q₂, 
    change f₁ One.star = f₂ One.star, apply λ p, ap10 p One.star, apply term_quot.unique,
    apply One.rec, exact rel }
end

/- We define the closure of an arbitrary relation to an equivalence relation, by 
   truncating the inductive family of sequences of relations on which transitivity can be 
   applied. -/
@[hott]
inductive trans_sequence {A : Type u} (R : A -> A -> trunctype.{u} -1) : 
  A -> A -> Type u
| rel {a b : A} (r : R a b) : trans_sequence a b
| refl (a : A) : trans_sequence a a
| symm {a b : A} (r : trans_sequence a b) : trans_sequence b a
| trans {a b c : A} (r : trans_sequence a b) (r' : trans_sequence b c) : 
                                                                    trans_sequence a c

@[hott]  --[GEVE]
def rel_to_equiv_rel {A : Type u} (R : A -> A -> trunctype.{u} -1) : A -> A -> Prop :=
  λ a b, ∥ trans_sequence R a b ∥

@[hott, instance]
def clos_rel_is_equiv_rel {A : Type u} (R : A -> A -> trunctype.{u} -1) : 
  is_equivalence (λ a b, rel_to_equiv_rel R a b) :=
begin
  fapply is_equivalence.mk,
  { intro a, exact tr (trans_sequence.refl R a) },
  { intros a b tr_seq, hinduction tr_seq with seq, exact tr (trans_sequence.symm seq) },
  { intros a b c tr_seq₁ tr_seq₂, 
    hinduction tr_seq₁ with seq₁, hinduction tr_seq₂ with seq₂,
    exact tr (trans_sequence.trans seq₁ seq₂) }
end 

/- The set-quotient to a general relation is a (constructively characterized) set-quotient 
   by the closure of the relation. To characterize the equality of quotient elements, we 
   descend the relation to the quotient, as above. -/
@[hott, reducible]
def rel_to_set_quotient_rel {A : Set} (R : A → A → Prop) : 
  (set_quotient R) -> (set_quotient R) -> Prop :=
begin
  let R' := λ a b : A, (rel_to_equiv_rel R a b).carrier,
  fapply @set_quotient.rec2 A R, 
  { exact rel_to_equiv_rel R },
  { intros a a' b H, apply pathover_of_eq, apply prop_iff_eq, 
    { intro H', exact rel_trans R' (rel_symm R' (tr (trans_sequence.rel H))) H' },
    { intro H', exact rel_trans R' (tr (trans_sequence.rel H)) H' } },
  { intros a a' b H, apply pathover_of_eq, apply prop_iff_eq, 
    { intro H', exact rel_trans R' H' (tr (trans_sequence.rel H)) },
    { intro H', exact rel_trans R' H' (rel_symm R' (tr (trans_sequence.rel H))) } } 
end

@[hott, reducible]
def rel_quot_rel_to_setquot_eq {A : Set} (R : A → A → Prop) : Π x y : set_quotient R,
  (rel_to_set_quotient_rel R x y) -> (x = y) :=
begin
  let R' := λ a b : A, (rel_to_equiv_rel R a b).carrier,
  let HP := λ (a b : A), @is_prop_map 
            (rel_to_set_quotient_rel R (set_class_of R a) (set_class_of R b)) 
            ((set_class_of R a) = (set_class_of R b)) _,
  intros x y,  
  fapply @set_quotient.rec2 A R 
         (λ x y : set_quotient R, (rel_to_set_quotient_rel R x y) -> (x = y)), 
  { intros a b H, hinduction H with tr_rel, hinduction tr_rel, 
    { exact eq_of_setrel R r },
    { exact idp },
    { exact ih⁻¹ },
    { exact ih_r ⬝ ih_r' }},
  { intros a a' b Ha, apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { intros a b b' Hb, apply pathover_of_tr_eq, exact is_prop.elim _ _  },
  { apply is_prop.mk, intros p q, exact is_set.elim _ _ }
end  

@[hott, reducible]
def rel_quot_eq_eqv_rel_quot_rel {A : Set} (R : A → A → Prop) : Π x y : set_quotient R,
  (x = y) ≃ (rel_to_set_quotient_rel R x y) :=
begin
  let R' := λ a b : A, (rel_to_equiv_rel R a b).carrier,
  let Rq := rel_to_set_quotient_rel R,
  have Rq_symm : Π x : set_quotient R, Rq x x, from 
    begin 
      intro x, hinduction x with q, hinduction q, 
      { change R' a a, exact rel_refl R' a },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
    end,
  intros x y, apply prop_iff_equiv, apply iff.intro,
    { intro p, rwr p, exact Rq_symm y },
    { exact rel_quot_rel_to_setquot_eq R x y }  
end

@[hott]
def class_eq_clos_rel {A : Set} (R : A → A → Prop) : 
  Π a b : A, set_class_of R a = set_class_of R b ≃ (rel_to_equiv_rel R) a b :=
begin
  intros a b, fapply prop_iff_equiv, fapply prod.mk,
  { intro p, 
    exact (rel_quot_eq_eqv_rel_quot_rel R (set_class_of R a) (set_class_of R b)).to_fun p },
  { intro rel, hinduction rel with tr_rel, hinduction tr_rel,
    { exact eq_of_setrel R r },
    { exact idp },
    { exact ih⁻¹ },
    { exact ih_r ⬝ ih_r' } }
end

@[hott]  --[GEVE]
def rel_set_quotient_is_cons_quotient {A : Set} (R : A -> A -> Prop) : 
  is_cons_quotient (rel_to_equiv_rel R) (set_quotient R) :=
begin
  fapply is_cons_quotient.mk, 
  { exact set_class_of R },
  { intro q, hinduction q with q, hinduction q, exact tr ⟨a, idp⟩, 
    apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { intros a b, fapply prod.mk,
    { intro class_eq, exact class_eq_clos_rel R a b class_eq },
    { intro rel, exact (class_eq_clos_rel R a b)⁻¹ᶠ rel } }
end  

/- We can define a quotient by an equivalence relation as the set of equivalence classes,
   given as a subset, that is a predicate `A -> Prop`. This quotient is a constructively 
   characterised quotient if we use propositional resizing (see [HoTT-Book,Thm.6.10.6]). -/
@[hott]
def is_equiv_class {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)]
  (P : A -> Prop) : Prop :=
∥ Σ (a : A), Π (b : A), R a b <-> P b ∥

@[hott]
def class_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] : 
  Set :=
Set.mk (Σ (P : A -> Prop), is_equiv_class R P) 
       (sigma.is_trunc_subtype (is_equiv_class R) -1) 

@[hott]  --[GEVE]
def class_is_cons_quotient {A : Set} (R : A → A → Prop) [is_equivalence (λ a b : A, R a b)] :
  is_cons_quotient R (class_quotient R) :=
begin
  fapply is_cons_quotient.mk,
  { intro a, fapply dpair,
    { exact λ b, R a b },
    { exact tr ⟨a, λ b, prod.mk id id⟩ } },
  { intro q, hinduction q with P is_class, hinduction is_class with rep, 
    hinduction rep with a eqv, apply tr, fapply dpair a,
    fapply sigma.sigma_eq,
    { apply eq_of_homotopy, intro b, exact iff_eq (eqv b) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros a₁ a₂, fapply prod.mk, 
    { intro p, have q : R a₁ = R a₂, from ap sigma.fst p,
      rwr q, exact rel_refl (λ a b : A, R a b) a₂ },
    { intro rel, fapply sigma.sigma_eq,
      { apply eq_of_homotopy, intro b, hsimp, 
        apply iff_eq, fapply prod.mk,
        { exact λ rel₁, rel_trans (λ a b : A, R a b) (rel_symm (λ a b : A, R a b) rel) rel₁ },
        { exact λ rel₂, rel_trans (λ a b : A, R a b) rel rel₂ } },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

end set

end hott