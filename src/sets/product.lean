import hott.init sets.basic

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc set

/- We characterize products of two types in four different ways, using their constructors, 
   induction principle, projections and universal properties, and show that they 
   (transitively) imply each other. -/
@[hott]  --[GEVE]
structure is_cons_product (A B P : Type _) :=
  (pair : A -> B -> P)
  (gens : Π (p : P), Σ (a : A) (b : B), p = pair a b)
  (free : Π {a₁ a₂ : A} {b₁ b₂ : B}, pair a₁ b₁ = pair a₂ b₂ -> (a₁ = a₂) × (b₁ = b₂))

@[hott]  --[GEVE]
def cons_prod_proj {A B P : Type _} (is_prod : is_cons_product A B P) :
  Σ (left : P -> A) (right : P -> B), Π (a : A) (b : B), (left (is_prod.pair a b) = a) ×
                                                         (right (is_prod.pair a b) = b) :=
begin  
  fapply dpair,
  { intro p, exact (is_prod.gens p).1 },
  { fapply dpair,
    { intro p, exact (is_prod.gens p).2.1 },
    { intros a b, fapply prod.mk,
      { exact (is_prod.free (is_prod.gens (is_prod.pair a b)).2.2).1⁻¹ },
      { exact (is_prod.free (is_prod.gens (is_prod.pair a b)).2.2).2⁻¹ } } }                                                         
end

@[hott]  --[GEVE]
def prod_is_cons_product (A B : Type _) : is_cons_product A B (A × B) :=
begin
  fapply is_cons_product.mk, 
  { exact prod.mk },
  { intro p, hinduction p, exact dpair fst (dpair snd idp) },
  { intros a₁ a₂ b₁ b₂ pair_eq, fapply prod.mk,
    { exact ap prod.fst pair_eq },
    { exact ap prod.snd pair_eq } }
end

@[hott]  --[GEVE]
structure is_ind_product (A B P : Type _) :=
  (pair : A -> B -> P)
  (map : Π {Q : Type _} (g : A -> B -> Q), Σ (h : P -> Q), 
           Π (a : A) (b : B), g a b = h (pair a b))
  (unique : Π {Q : Type _} (h₁ h₂ : P -> Q),
               (Π (a : A) (b : B), h₁ (pair a b) = h₂ (pair a b)) -> h₁ = h₂)

@[hott] --[GEVE]
def cons_ind_product_equiv (A B P : Type _) : 
  is_cons_product A B P <-> is_ind_product A B P :=
begin
  fapply prod.mk,
  { intro P_prod, fapply is_ind_product.mk,
    { exact P_prod.pair },
    { intros Q g, fapply dpair,
      { intro p, exact g ((cons_prod_proj P_prod).1 p) ((cons_prod_proj P_prod).2.1 p) },
      { intros a b, fapply ap011, rwr ((cons_prod_proj P_prod).2.2 a b).1, 
                                  rwr ((cons_prod_proj P_prod).2.2 a b).2 } },
    { intros Q h₁ h₂ h_eq, apply eq_of_homotopy, intro p,
      have p_eq : p = P_prod.pair (P_prod.gens p).1 (P_prod.gens p).2.1, from 
        (P_prod.gens p).2.2,
      rwr p_eq, exact h_eq _ _ } },
  { intro P_prod, fapply is_cons_product.mk, 
    { exact P_prod.pair },
    { intro p, fapply dpair,
      { exact (P_prod.map (λ a b, a)).1 p },
      { fapply dpair,
        { exact (P_prod.map (λ a b, b)).1 p },
        { let h₁ : P -> A × B := λ p, prod.mk ((P_prod.map (λ a b, a)).1 p) 
                                              ((P_prod.map (λ a b, b)).1 p),
          let h₂ : A × B -> P := λ ab, P_prod.pair (prod.fst ab) (prod.snd ab),
          apply @ap10 _ _ (λ p, p) (h₂ ∘ h₁), apply P_prod.unique, intros a b, 
          apply ap011,  
          change _ = (P_prod.map (λ a b, a)).1 _ , rwr <- (P_prod.map (λ a b, a)).2 a b, 
          change _ = (P_prod.map (λ a b, b)).1 _ , rwr <- (P_prod.map (λ a b, b)).2 a b } } },
    { intros a₁ a₂ b₁ b₂ pair_eq, fapply prod.mk,
      { change (λ a b, a) a₁ b₁ = (λ a b, a) a₂ b₂, 
        rwr (P_prod.map (λ a b, a)).2 a₁ b₁, rwr (P_prod.map (λ a b, a)).2 a₂ b₂, 
        exact ap (P_prod.map (λ a b, a)).1 pair_eq },
      { change (λ a b, b) a₁ b₁ = (λ a b, b) a₂ b₂, 
        rwr (P_prod.map (λ a b, b)).2 a₁ b₁, rwr (P_prod.map (λ a b, b)).2 a₂ b₂, 
        exact ap (P_prod.map (λ a b, b)).1 pair_eq } } }
end 

@[hott]  --[GEVE]
structure is_product (A B P : Type _) :=
  (fst : P -> A)
  (snd : P -> B)
  (pair_exists : Π (a : A) (b : B), Σ (p : P), (fst p = a) × (snd p = b))
  (pair_unique : Π (p p' : P), fst p = fst p' -> snd p = snd p' -> p = p')

@[hott, reducible]
def type_product_is_product (A B : Type _) : is_product A B (A × B) :=
begin
  fapply is_product.mk,
  { exact prod.fst },
  { exact prod.snd },
  { intros a b, fapply sigma.mk, 
    { exact ⟨a, b⟩ },
    { exact ⟨idp, idp⟩ } },
  { intros p p' p1 p2, hinduction p, hinduction p',
    fapply prod.pair_eq, exact p1, exact p2 } 
end

@[hott] --[GEVE]
structure is_proj_univ_product (A B P : Type _) :=
  (fst : P -> A)
  (snd : P -> B)
  (factors : Π {Q : Type _} (q_A : Q -> A) (q_B : Q -> B), Σ (q_P : Q -> P), Π (q : Q),
               (fst (q_P q) = q_A q) × (snd (q_P q) = q_B q))
  (unique : Π {Q : Type _} (q_A : Q -> A) (q_B : Q -> B) (q_P q_P' : Q -> P),
               fst ∘ q_P = fst ∘ q_P' -> snd ∘ q_P = snd ∘ q_P' -> q_P = q_P')

@[hott, reducible] --[GEVE]
def equiv_char_of_products (A B P : Type _) : 
  is_product A B P <-> is_proj_univ_product A B P :=
begin  
  fapply prod.mk,
  { intro is_prod, fapply is_proj_univ_product.mk,
    { exact is_prod.fst },
    { exact is_prod.snd },
    { intros Q qA qB, fapply dpair,
      { intro q, exact (@is_product.pair_exists _ _ _ is_prod (qA q) (qB q)).1 },
      { intro q, fapply prod.mk, 
        { exact (@is_product.pair_exists _ _ _ is_prod (qA q) (qB q)).2.1 }, 
        { exact (@is_product.pair_exists _ _ _ is_prod (qA q) (qB q)).2.2 } } },
    { intros Q qA qB qP qP' qAP qBP, apply eq_of_homotopy, intro q,
      exact @is_product.pair_unique _ _ _ is_prod (qP q) (qP' q) (ap10 qAP q) (ap10 qBP q) } },
  { intro is_prod', fapply is_product.mk,
    { exact is_prod'.fst },
    { exact is_prod'.snd },
    { intros a b, fapply dpair,
      { exact (is_proj_univ_product.factors is_prod' (@One.rec (λ n, A) a) 
                                            (@One.rec (λ n, B) b)).1 One.star },
      { exact (is_proj_univ_product.factors is_prod' (@One.rec (λ n, A) a) 
                                            (@One.rec (λ n, B) b)).2 One.star } },
    { intros p p' pa pb, 
      let qA := @One.rec (λ n, A) (is_prod'.fst p), 
      let qB := @One.rec (λ n, B) (is_prod'.snd p),
      let qP := @One.rec (λ n, P) p, let qP' := @One.rec (λ n, P) p',
      let qAP := @One.rec (λ n, is_prod'.fst (qP n) = is_prod'.fst (qP' n)) pa,
      let qBP := @One.rec (λ n, is_prod'.snd (qP n) = is_prod'.snd (qP' n)) pb,
      exact @ap10 One P _ _ (@is_proj_univ_product.unique _ _ _ is_prod' _ qA qB qP qP'
                        (eq_of_homotopy qAP) (eq_of_homotopy qBP)) One.star } }
end

@[hott, reducible]
def product_map {A B P Q : Type _} : is_product A B P -> is_product A B Q -> P -> Q :=
  λ is_prod_P is_prod_Q p, (is_prod_Q.pair_exists (is_prod_P.fst p) (is_prod_P.snd p)).1

@[hott]  --[GEVE]
def product_map.right_inv {A B P Q : Type _} : Π (is_prod_P : is_product A B P) 
  (is_prod_Q : is_product A B Q), 
  product_map is_prod_P is_prod_Q ∘ product_map is_prod_Q is_prod_P = @id Q :=
begin    
  intros is_prod_P is_prod_Q, apply eq_of_homotopy, intro q,
  change (is_prod_Q.pair_exists (is_prod_P.fst (is_prod_P.pair_exists _ _).1) 
                                (is_prod_P.snd (is_prod_P.pair_exists _ _).1)).1 = q, 
  fapply @is_product.pair_unique _ _ _ is_prod_Q _ q, 
  { rwr (is_prod_Q.pair_exists _ _).2.1, rwr (is_prod_P.pair_exists _ _).2.1 },
  { rwr (is_prod_Q.pair_exists _ _).2.2, rwr (is_prod_P.pair_exists _ _).2.2 }
end

@[hott]  --[GEVE]
def product_map.left_inv {A B P Q : Type _} : Π (is_prod_P : is_product A B P) 
  (is_prod_Q : is_product A B Q), 
  product_map is_prod_Q is_prod_P ∘ product_map is_prod_P is_prod_Q = @id P :=
λ is_prod_P is_prod_Q, product_map.right_inv is_prod_Q is_prod_P

@[hott, reducible]  --[GEVE]
def product_eq {A B P Q : Type _} : Π (is_prod_P : is_product A B P) 
  (is_prod_Q : is_product A B Q), P = Q :=
begin
 intros is_prod_P is_prod_Q, apply ua, fapply equiv.mk,
    { exact product_map is_prod_P is_prod_Q },
    { fapply adjointify,
      { exact product_map is_prod_Q is_prod_P },
      { intro q, exact ap10 (product_map.right_inv is_prod_P is_prod_Q) q },
      { intro p, exact ap10 (product_map.left_inv is_prod_P is_prod_Q) p } }
end 

/- These (quasi-)inverses can be used to construct an equivalence and hence by univalence 
   equality between two products. To make such an equality unique ("canonical") we need
   to restrict the factors of the product to sets. Using the Structure Identity Principle
   we can even show that the whole structure of a set product can be contracted to the
   inductive construction of a (set) product. -/
@[hott]
structure Set_product (A B : Set) :=
  (carrier : Set)
  (is_prod : is_product A B carrier)

@[hott, reducible]
def ind_Set_product (A B : Set) := Set_product.mk (A × B) (type_product_is_product A B)

@[hott]
def Set_Product_equiv_Sigma (A B : Set) : 
  Set_product A B ≃ Σ (P : Set), is_product A B P := 
begin
  fapply equiv.mk, 
  { intro Product, exact dpair Product.carrier Product.is_prod },
  { fapply adjointify,
    { intro Sigma_prod, exact Set_product.mk Sigma_prod.1 Sigma_prod.2 },
    { intro Sigma_prod, hinduction Sigma_prod with P is_prod_P, exact idp },
    { intro Product, hinduction Product with P is_prod_P, exact idp } }
end

@[hott]  --[GEVE]
def Product_dep_id_sys (A B : Set) : 
  @dep_ppred Set (A × B) (λ P, is_product A B P) (type_product_is_product A B) :=
begin 
  fapply dep_ppred.mk,
  { exact id_ppred (A × B) },
  { intros P is_prod_P p, 
    exact prod (set.Prod_set.fst A B =[p; λ P : Set, P -> A] is_prod_P.fst) 
               (set.Prod_set.snd A B =[p; λ P : Set, P -> B] is_prod_P.snd) },
  { exact ⟨idpo, idpo⟩ } 
end

@[hott, instance]
def product_eq_contr (A B : Set) : is_contr (Σ (is_prod : is_product A B (A × B)), 
  (Product_dep_id_sys A B).dep_fam (A × B) is_prod (Product_dep_id_sys A B).ppred_fst.base) :=
begin
  fapply is_contr.mk,
  { exact dpair (type_product_is_product A B) (pair idpo idpo) },
  { intro a, hinduction a with is_pr_pr comp_pair, 
    change prod (_ =[idp] _) (_ =[idp] _) at comp_pair,
    fapply sigma.sigma_eq,
    { hinduction is_pr_pr, 
      have q₁ : set.Prod_set.fst A B = fst, from eq_of_pathover_idp comp_pair.1,
      have q₂ : set.Prod_set.snd A B = snd, from eq_of_pathover_idp comp_pair.2, 
      hinduction q₁, hinduction q₂,   
      fapply ap0111 is_product.mk,
      { exact idp },
      { exact idp },
      { change _ =[idp] _, apply pathover_idp_of_eq, apply eq_of_homotopy2,
        intros a b, fapply sigma.sigma_eq, 
        { fapply pair_unique, rwr (pair_exists a b).2.1, rwr (pair_exists a b).2.2 },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { change _ =[_; λ a, prod (_ =[idp] _) (_ =[idp] _)] _, 
      apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott]
def product_eq_proj_eq {A B : Set} (P_prod : Σ (P : Set), is_product A B P) : 
  Σ (p : (A × B : Set) = P_prod.1), 
  (Product_dep_id_sys A B).dep_fam P_prod.fst P_prod.snd p := 
begin 
  fapply dpair,
  { apply set.car_eq_to_set_eq, exact product_eq (type_product_is_product A B) P_prod.snd },
  { fapply prod.mk,
    { apply pathover_of_pathover_ap (λ P : Type _, P -> A) trunctype.carrier,
      change _ =[set.set_eq_equiv_car_eq.to_fun ((set.set_eq_equiv_car_eq.to_fun)⁻¹ᶠ _)] _,
      rwr set.set_eq_equiv_car_eq.to_is_equiv.right_inv,
      apply fn_pathover_equiv_of_eq, rwr equiv_of_eq_ua, apply eq_of_homotopy, intro p, 
      change _ = P_prod.2.fst (P_prod.2.pair_exists _ _).1, 
      rwr (P_prod.2.pair_exists _ _).2.1 },
    { apply pathover_of_pathover_ap (λ P : Type _, P -> B) trunctype.carrier,
      change _ =[set.set_eq_equiv_car_eq.to_fun ((set.set_eq_equiv_car_eq.to_fun)⁻¹ᶠ _)] _,
      rwr set.set_eq_equiv_car_eq.to_is_equiv.right_inv,
      apply fn_pathover_equiv_of_eq, rwr equiv_of_eq_ua, apply eq_of_homotopy, intro p, 
      change _ = P_prod.2.snd (P_prod.2.pair_exists _ _).1, 
      rwr (P_prod.2.pair_exists _ _).2.2 } }
end

@[hott, instance]  --[GEVE]
def Set_products_are_canonically_equal (A B : Set) : is_contr (Set_product A B) :=
begin 
  apply is_trunc_equiv_closed_rev -2 (Set_Product_equiv_Sigma A B),
  fapply is_contr.mk,
  { exact dpair (A × B) (type_product_is_product A B) },
  { intro P_prod, 
    exact (struct_id_char_of_contr _ (Product_dep_id_sys A B) (is_contr_tot_peq _) 
            (product_eq_contr A B) P_prod)⁻¹ᶠ (product_eq_proj_eq P_prod) }
end

/- Characterisations of triple products by universal properties derived from the 
   constructors and from the inductive principle are equivalent, but not the most effective 
   ones: Iterating the constructive characterisation of the ordinary product of two 
   factors gives an easy proof of uniqueness of triple products of sets. -/
@[hott]  --[GEVE]
structure is_triple_product (A B C P : Type _) := 
  (fst : P -> A)
  (snd : P -> B)
  (trd : P -> C)
  (triple_exists : Π (a : A) (b : B) (c : C), 
                                     Σ (p : P), (fst p = a) × (snd p = b) × (trd p = c))
  (triple_unique : Π (p p' : P), (fst p = fst p') -> (snd p = snd p') -> (trd p = trd p') ->
                                  p = p')

@[hott]  --[GEVE]
structure is_triple_product' (A B C P : Type _) := 
  (fst : P -> A)
  (snd : P -> B)
  (trd : P -> C)
  (factors : Π {Q : Type _} {qA : Q -> A} {qB : Q -> B} {qC : Q -> C}, Σ (qP : Q -> P), 
          Π (q : Q), (fst (qP q) = qA q) × (snd (qP q) = qB q) × (trd (qP q) = qC q))
  (unique : Π {Q : Type _} {qA : Q -> A} {qB : Q -> B} {qC : Q -> C} (qP qP' : Q -> P),
           fst ∘ qP = fst ∘ qP' -> snd ∘ qP = snd ∘ qP' -> trd ∘ qP = trd ∘ qP' -> qP = qP')

@[hott, reducible] --[GEVE]
def equiv_char_of_triple_products (A B C P : Type _) : 
  is_triple_product A B C P <-> is_triple_product' A B C P :=
begin  
  fapply prod.mk,
  { intro is_prod, fapply is_triple_product'.mk,
    { exact is_prod.fst },
    { exact is_prod.snd },
    { exact is_prod.trd },
    { intros Q qA qB qC, fapply dpair,
      { intro q, exact (is_prod.triple_exists (qA q) (qB q) (qC q)).1 },
      { intro q, fapply prod.mk, 
        { exact (is_prod.triple_exists (qA q) (qB q) (qC q)).2.1 }, 
        { exact (is_prod.triple_exists (qA q) (qB q) (qC q)).2.2 } } },
    { intros Q qA qB qC qP qP' qAP qBP qCP, apply eq_of_homotopy, intro q,
      exact @is_triple_product.triple_unique _ _ _ _ is_prod (qP q) (qP' q) 
              (ap10 qAP q) (ap10 qBP q) (ap10 qCP q) } },
  { intro is_prod', fapply is_triple_product.mk,
    { exact is_prod'.fst },
    { exact is_prod'.snd },
    { exact is_prod'.trd },
    { intros a b c, fapply dpair,
      { exact (@is_triple_product'.factors _ _ _ _ is_prod' _ (@One.rec (λ n, A) a) 
                            (@One.rec (λ n, B) b) (@One.rec (λ n, C) c)).1 One.star },
      { exact (@is_triple_product'.factors _ _ _ _ is_prod' _ (@One.rec (λ n, A) a) 
                            (@One.rec (λ n, B) b) (@One.rec (λ n, C) c)).2 One.star } },
    { intros p p' pa pb pc, 
      let qA := @One.rec (λ n, A) (is_prod'.fst p), 
      let qB := @One.rec (λ n, B) (is_prod'.snd p),
      let qC := @One.rec (λ n, C) (is_prod'.trd p),
      let qP := @One.rec (λ n, P) p, let qP' := @One.rec (λ n, P) p',
      let qAP := @One.rec (λ n, is_prod'.fst (qP n) = is_prod'.fst (qP' n)) pa,
      let qBP := @One.rec (λ n, is_prod'.snd (qP n) = is_prod'.snd (qP' n)) pb,
      let qCP := @One.rec (λ n, is_prod'.trd (qP n) = is_prod'.trd (qP' n)) pc,
      exact @ap10 One P _ _ (@is_triple_product'.unique _ _ _ _ is_prod' _ qA qB qC qP qP'
               (eq_of_homotopy qAP) (eq_of_homotopy qBP) (eq_of_homotopy qCP)) One.star } }
end                                                                     

@[hott]
structure triple_Set_product (A B C : Set) :=
  (carrier : Set)
  (is_triple_prod : is_triple_product A B C carrier)

@[hott]  --[GEVE]
structure left_triple_Set_product (A B C : Set) :=
  (left_prod : Set_product A B)
  (prod : Set_product left_prod.carrier C)

@[hott, reducible]
def ind_left_triple_Set_product (A B C : Set) : left_triple_Set_product A B C :=
  left_triple_Set_product.mk (ind_Set_product A B) (ind_Set_product (A × B) C) 

@[hott, instance]  --[GEVE]
def left_triple_Set_products_are_canonically_equal (A B C : Set) : 
  is_contr (left_triple_Set_product A B C) :=
begin
  fapply is_contr.mk,
  { exact ind_left_triple_Set_product A B C },
  { intro P_prod, hinduction P_prod, change left_triple_Set_product.mk _ _ = _,
    have p : ind_Set_product A B = left_prod, from is_prop.elim _ _,
    hinduction p,
    fapply apd011 left_triple_Set_product.mk, 
    { exact idp },
    { apply pathover_idp_of_eq, exact is_prop.elim _ _ } }
end

/- The construction of an equivalence between iterated and constructive characterisation 
   of triple products uses the standard arguments showing that `(A × B) × C` is a 
   triple product. -/

@[hott, reducible]  --[GEVE]
def triple_Set_product_to_left (A B C : Set) :
  triple_Set_product A B C -> left_triple_Set_product A B C :=
begin
intro P, fapply left_triple_Set_product.mk,
{ exact ind_Set_product A B },
{ fapply Set_product.mk,
  { exact P.carrier },
  { fapply is_product.mk,
    { intro p, exact ((type_product_is_product A B).pair_exists 
                    (P.is_triple_prod.fst p) (P.is_triple_prod.snd p)).1 },
    { exact P.is_triple_prod.trd },
    { intros ab c, fapply dpair,
      { exact (P.is_triple_prod.triple_exists 
                            ((type_product_is_product A B).fst ab) 
                            ((type_product_is_product A B).snd ab) c).1 },
      { fapply prod.mk, 
        { rwr (P.is_triple_prod.triple_exists ab.fst ab.snd c).2.1,
          rwr (P.is_triple_prod.triple_exists ab.fst ab.snd c).2.2.1,
          hinduction ab, exact idp }, 
        { rwr (P.is_triple_prod.triple_exists ab.fst ab.snd c).2.2.2 } } },
    { intros p p' fst_snd_eq trd_eq,
      fapply P.is_triple_prod.triple_unique, 
      { exact ap prod.fst fst_snd_eq },
      { exact ap prod.snd fst_snd_eq },
      { assumption } } } }
end

@[hott, reducible]  --[GEVE]
def left_to_triple_Set_product (A B C : Set) :
  left_triple_Set_product A B C -> triple_Set_product A B C :=
begin
  intro P, 
  fapply triple_Set_product.mk,
  { exact P.prod.carrier },
  { fapply is_triple_product.mk, 
    { exact P.left_prod.is_prod.fst ∘ P.prod.is_prod.fst },
    { exact P.left_prod.is_prod.snd ∘ P.prod.is_prod.fst },
    { exact P.prod.is_prod.snd },
    { intros a b c, fapply dpair,
      { exact (P.prod.is_prod.pair_exists 
                     (P.left_prod.is_prod.pair_exists a b).1 c).1 },
      { fapply prod.mk, 
        { change P.left_prod.is_prod.fst (P.prod.is_prod.fst _) = _,
          rwr (P.prod.is_prod.pair_exists _ c).2.1, 
          rwr (P.left_prod.is_prod.pair_exists _ _).2.1 },
        { fapply prod.mk,
          { change P.left_prod.is_prod.snd (P.prod.is_prod.fst _) = _,
            rwr (P.prod.is_prod.pair_exists _ c).2.1, 
            rwr (P.left_prod.is_prod.pair_exists _ _).2.2 },
          { rwr (P.prod.is_prod.pair_exists _ c).2.2 } } } },
    { intros p p' fst_eq snd_eq trd_eq, fapply P.prod.is_prod.pair_unique,
      { fapply P.left_prod.is_prod.pair_unique, 
        { assumption },
        { assumption } },
      { assumption } } }
end

@[hott]
def triple_Set_product_equiv_left (A B C : Set) :
  triple_Set_product A B C ≃ left_triple_Set_product A B C :=
begin
  fapply equiv.mk,
  { exact triple_Set_product_to_left A B C },
  { fapply adjointify, 
    { exact left_to_triple_Set_product A B C },
    { intro P, exact @eq_of_is_contr _ 
                  (left_triple_Set_products_are_canonically_equal A B C) _ _ },
    { intro P, hinduction P with P P_prod, fapply apd011 triple_Set_product.mk, 
      { exact idp },
      { apply pathover_idp_of_eq, 
        hinduction P_prod with fst snd trd triple_exists triple_unique,
        hsimp, fapply apd011111 is_triple_product.mk, 
        { exact idp },
        { exact idp },
        { exact idp },
        { apply pathover_idp_of_eq, apply eq_of_homotopy3, intros a b c, 
          fapply sigma.sigma_eq,
          { exact idp },
          { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } } }
end

@[hott]
def triple_Set_products_are_canonically_equal (A B C P : Set) : 
  is_contr (triple_Set_product A B C) :=
is_trunc_equiv_closed_rev -2 (triple_Set_product_equiv_left A B C)
                      (left_triple_Set_products_are_canonically_equal A B C)

/- Moving brackets in iterated triple products leads to equivalent types, as can be 
   directly derived from the uniqueness properties of ordinary products of sets. -/
@[hott]  --[GEVE]
structure right_triple_Set_product (A B C : Set) :=
  (right_prod : Set_product B C)
  (prod : Set_product A right_prod.carrier)

@[hott, reducible]
def ind_right_triple_Set_product (A B C : Set) : right_triple_Set_product A B C :=
  right_triple_Set_product.mk (Set_product.mk (B × C) (type_product_is_product B C))
                      (Set_product.mk (A × B × C) (type_product_is_product A (B × C))) 

@[hott]  --[GEVE]
def left_equiv_right_triple_Set_product (A B C : Set) : 
  left_triple_Set_product A B C ≃ right_triple_Set_product A B C :=
begin
  fapply equiv.mk,
  { intro P, fapply right_triple_Set_product.mk, 
    { exact ind_Set_product B C },
    { exact ind_Set_product A (B × C) } },
  { fapply adjointify, 
    { intro P, fapply left_triple_Set_product.mk,
      { exact ind_Set_product A B },
      { exact ind_Set_product (A × B) C } },
    { intro P_prod, hinduction P_prod with P_right_prod P_prod, 
      fapply apd011 right_triple_Set_product.mk, 
      { exact is_prop.elim _ _ },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intro P_prod, hinduction P_prod with P_left_prod P_prod, 
      fapply apd011 left_triple_Set_product.mk, 
      { exact is_prop.elim _ _ },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

end hott