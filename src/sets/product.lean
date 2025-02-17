import sets.basic

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

@[hott]
def cons_prod_pair_eq {A B P : Type _} (is_prod : is_cons_product A B P) :
  Π (p : P), 
      p = is_prod.pair ((cons_prod_proj is_prod).1 p) ((cons_prod_proj is_prod).2.1 p) :=
begin 
  intro p, change p = is_prod.pair (is_prod.gens p).1 (is_prod.gens p).2.1, 
  exact (is_prod.gens p).2.2 
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

@[hott]
def cons_product_equiv_product (A B P : Type _) : 
  is_cons_product A B P <-> is_product A B P :=
begin
  fapply prod.mk,
  { intro is_prod, fapply is_product.mk,
    { exact (cons_prod_proj is_prod).1 },
    { exact (cons_prod_proj is_prod).2.1 },
    { intros a b, fapply dpair (is_prod.pair a b), fapply prod.mk,
      { exact ((cons_prod_proj is_prod).2.2 a b).1 },
      { exact ((cons_prod_proj is_prod).2.2 a b).2 } },
    { intros p p' fst_eq snd_eq, 
      rwr cons_prod_pair_eq is_prod p, rwr cons_prod_pair_eq is_prod p',
      fapply ap011 is_prod.pair, exact fst_eq, exact snd_eq } },
  { intro is_prod, fapply is_cons_product.mk,
    { intros a b, exact (is_prod.pair_exists a b).1 },
    { intro p, fapply dpair (is_prod.fst p), fapply dpair (is_prod.snd p), 
      change p = (is_prod.pair_exists _ _).1, fapply is_prod.pair_unique,
      exact (is_prod.pair_exists _ _).2.1⁻¹, exact (is_prod.pair_exists _ _).2.2⁻¹ },
    { intros a₁ a₂ b₁ b₂ pair_eq, fapply prod.mk, 
      { rwr <- (is_prod.pair_exists a₁ b₁).2.1, rwr <- (is_prod.pair_exists a₂ b₂).2.1,
        exact ap is_prod.fst pair_eq },
      { rwr <- (is_prod.pair_exists a₁ b₁).2.2, rwr <- (is_prod.pair_exists a₂ b₂).2.2,
        exact ap is_prod.snd pair_eq } } }
end

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

/- Characterisations of products of finitely many sets by universal properties derived from the 
   constructors and from the inductive principle are equivalent. -/
@[hott]
structure is_cons_set_tuple_product {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u}) :=
  (tuple : (Π (i : fin n), A i) -> P)
  (gens : Π (p : P), Σ (t : Π (i : fin n), A i), tuple t = p)
  (free : Π (s t : Π (i : fin n), A i), (tuple s = tuple t) -> s = t)

@[hott]
def tuple_is_set_product {n : ℕ} (A : tuple Set.{u} n) : 
  is_cons_set_tuple_product A (set.tuple_Set A) :=
begin
  fapply is_cons_set_tuple_product.mk,
  { exact id },
  { intro p, exact ⟨p, idp⟩ },
  { intros s t q, exact q }
end

@[hott]
structure is_set_tuple_product {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u}) :=
  (proj : Π (i : fin n), P -> A i)
  (tuple_exists : Π (t : Π (i : fin n), A i), Σ (p : P), Π (i : fin n), proj i p = t i)
  (tuple_unique : Π (p p' : P), (Π (i : fin n), proj i p = proj i p') -> p = p')

@[hott]
def is_cons_equiv_is_set_tuple_product {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u}) :
  is_cons_set_tuple_product A P <-> is_set_tuple_product A P :=
begin
  fapply prod.mk,
  { intro is_prod, fapply is_set_tuple_product.mk,
    { intros i p, exact (is_prod.gens p).1 i },
    { intro t, fapply dpair (is_prod.tuple t), apply apd10,
      apply is_prod.free, exact (is_prod.gens _).2 },
    { intros p p' tuple_eq, rwr <- (is_prod.gens p).2, rwr <- (is_prod.gens p').2,
      apply ap is_prod.tuple, apply eq_of_homotopy, exact tuple_eq } },
  { intro is_prod, fapply is_cons_set_tuple_product.mk,
    { intro t, exact (is_prod.tuple_exists t).1 },
    { intro p, fapply dpair,
      { exact λ i, is_prod.proj i p },
      { apply is_prod.tuple_unique, intro i, exact ((is_prod.tuple_exists _).2 i) } },
    { intros s t tuple_eq, apply eq_of_homotopy, intro i,
      rwr <- ((is_prod.tuple_exists s).2 i), rwr <- ((is_prod.tuple_exists t).2 i), 
      exact ap (is_prod.proj i) tuple_eq } }
end

@[hott]
structure is_univ_set_tuple_product {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u}) :=
  (proj : Π (i : fin n), P -> A i)
  (factors : Π {Q : Set.{u}} (qA : Π (i : fin n), Q -> A i), Σ (qP : Q -> P),
               Π (q : Q) (i : fin n), proj i (qP q) = qA i q)
  (unique : Π {Q : Set.{u}} (qP qP' : Q -> P), (Π (i : fin n), 
              (proj i) ∘ qP = (proj i) ∘ qP') -> qP = qP')

@[hott]
def set_tuple_product_equiv_univ {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u}) : 
  is_set_tuple_product A P <-> is_univ_set_tuple_product A P :=
begin
  fapply prod.mk,
  { intro is_prod, fapply is_univ_set_tuple_product.mk,
    { exact is_prod.proj },
    { intros Q qA, fapply dpair,
      { intro q, exact (is_prod.tuple_exists (λ i, qA i q)).1 },
      { intros q i, exact (is_prod.tuple_exists _).2 i } },
    { intros Q qP qP' proj_eq, apply eq_of_homotopy, intro q,
      apply is_prod.tuple_unique, intro i, exact ap10 (proj_eq i) q } },
  { intro is_prod, fapply is_set_tuple_product.mk,
    { exact is_prod.proj },
    { intro t, fapply dpair,
      { exact (@is_univ_set_tuple_product.factors _ _ _ is_prod One_Set 
                                         (λ i, @One.rec (λ n, A i) (t i))).1 One.star },
      { exact (@is_univ_set_tuple_product.factors _ _ _ is_prod One_Set 
                                         (λ i, @One.rec (λ n, A i) (t i))).2 One.star } },
    { intros p p' proj_eq, 
      let qP := @One.rec (λ n, P) p, let qP' := @One.rec (λ n, P) p',
      change qP One.star = qP' One.star, apply λ q, apd10 q One.star, 
      apply @is_univ_set_tuple_product.unique _ _ _ is_prod One_Set, 
      intro i, apply eq_of_homotopy, intro o,
      have op : o = One.star, from @is_prop.elim _ One_is_prop _ _, rwr op,
      exact proj_eq i } }
end

/- The product of two sets can be characterised by 2-tuples = pairs, or directly from the 
   factors. -/
@[hott]
def is_tuple_product_equiv_is_pair_product {A B : Set.{u}} (P : Set.{u}) :
  is_cons_set_tuple_product (tuple_of_list [A, B]) P <-> is_cons_product A B P :=
begin
  fapply prod.mk,
  { intro is_prod, fapply is_cons_product.mk,
    { intros a b, exact is_prod.tuple (λ i, cast (tuple_of_list.map 
                                 (λ A : Set, A.carrier) [A, B] i) (fin_map_two a b _)) },
    { intro p, fapply dpair,
      { exact (is_prod.gens p).1 (fin.mk 0 (nat.zero_lt_succ 1)) },
      { fapply dpair,
        { exact (is_prod.gens p).1 (fin.mk 1 (nat.le_refl 2)) },
        { apply λ q, (is_prod.gens p).2⁻¹ ⬝ q, apply ap is_prod.tuple, 
          apply eq_of_homotopy, intro i, change _ = hott.eq.cast _ _, 
          hinduction i with i is_lt, hinduction i, 
          { change _ = hott.eq.cast (@idp _ A.carrier) ((is_prod.gens p).1 (fin.mk 0 _)),
            have q : is_lt = nat.zero_lt_succ 1, from is_prop.elim _ _, rwr q },
          { hinduction n,
            { change _ = hott.eq.cast _ ((is_prod.gens p).1 (fin.mk 1 _)), 
              have q : is_lt = nat.le_refl 2, from is_prop.elim _ _, rwr q },
            { change n + 2 < 2 + 0 at is_lt, rwr nat.add_comm n 2 at is_lt, 
              hinduction nat.not_lt_zero n (nat.lt_of_add_lt_add_left is_lt) } } } } },
    { intros a₁ a₂ b₁ b₂ tuple_eq, fapply prod.mk,
      exact apd10 (is_prod.free _ _ tuple_eq) (fin.mk 0 (nat.zero_lt_succ 1)), 
      exact apd10 (is_prod.free _ _ tuple_eq) (fin.mk 1 (nat.le_refl 2)) } },
  { intro is_prod, fapply is_cons_set_tuple_product.mk,
    { intro t, exact is_prod.pair (t (fin.mk 0 (nat.zero_lt_succ 1))) 
                                  (t (fin.mk 1 (nat.le_refl 2))) },
    { intro p, fapply dpair,
      { exact λ i, hott.eq.cast (tuple_of_list.map (λ A : Set, A.carrier) [A, B] i) 
                (fin_map_two (is_prod.gens p).1 (is_prod.gens p).2.1 (fin.mk i.val _)) },
      { let q := (is_prod.gens p).2.2, rwr q } },
    { intros s t pair_eq, apply eq_of_homotopy, intro i, hinduction i with i is_lt,
      hinduction i, 
      { have q : is_lt = nat.zero_lt_succ 1, from is_prop.elim _ _, rwr q,
        exact (is_prod.free pair_eq).1 },
      { hinduction n,
        { have q : is_lt = nat.le_refl 2, from is_prop.elim _ _, rwr q,
          exact (is_prod.free pair_eq).2 },
        { change n + 2 < 2 + 0 at is_lt, rwr nat.add_comm n 2 at is_lt, 
          hinduction nat.not_lt_zero n (nat.lt_of_add_lt_add_left is_lt) } } } } 
end

/- Nested constructions of products of finitely many sets are possible. -/
@[hott]
def fin_map.split_left {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} : 
  (Π (i : fin (n + m)), tuple.append A B i) -> Π (i : fin n), A i :=
λ t i, (tuple.append_left A B i) ▸ t (fin_lift i)

@[hott]
def fin_map.split_right {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} : 
  (Π (i : fin (n + m)), tuple.append A B i) -> Π (i : fin m), B i :=
λ t i, (tuple.append_right A B i) ▸ t (fin_lift_rev i) 

@[hott, hsimp]
def fin_map.append {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} : 
  (Π (i : fin n), A i) -> (Π (i : fin m), B i) -> 
  (Π (i : fin (n + m)), tuple.append A B i) :=
begin
  intros s t i, 
  fapply @sum.rec (i.val < n) (i.val ≥ n) (λ s, @tuple.append Set _ _ A B i),
  { intro q, rwr <- fin_lift_desc i q, 
    rwr tuple.append_left A B (fin_desc i q), exact s _ },
  { intro q, rwr <- fin_lift_desc_rev i q,
    rwr tuple.append_right A B (fin_desc_rev i q), exact t _ },
  { exact nat.lt_sum_ge i.val n }
end

@[hott]
def fin_map.append_left {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} 
  (s : Π (i : fin n), A i) (t : Π (i : fin m), B i) : Π (i : fin n),
  (tuple.append_left A B i) ▸ (fin_map.append s t) (fin_lift i) = s i :=
begin
  intro i, 
  hinduction nat.lt_sum_ge (@fin_lift n m i).val n with in_sum q q,
  { apply tr_eq_of_eq_inv_tr, 
    change @sum.rec ((@fin_lift n m i).val < n) ((@fin_lift n m i).val ≥ n) 
                    (λ s, @tuple.append Set _ _ A B (@fin_lift n m i)) _ _ _ = _, 
    rwr in_sum, change _ ▸[λ i, @tuple.append Set n m A B i] _ = _, rwr eq.inv_inv,
    have p : fin_lift_desc (fin_lift i) q = ap fin_lift (fin_desc_lift i q), from 
      is_set.elim _ _, rwr p, rwr tr_ap, 
    exact apdt (λ i, (tuple.append_left A B i)⁻¹ ▸ s i) (fin_desc_lift i q) },
  { hinduction nat.lt_irrefl _ (nat.lt_of_le_of_lt q i.is_lt) }
end

@[hott]
def fin_map.append_right {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} 
  (s : Π (i : fin n), A i) (t : Π (i : fin m), B i) : Π (i : fin m),
  tuple.append_right A B i ▸ fin_map.append s t (fin_lift_rev i) = t i :=
begin
  intro i, 
  hinduction nat.lt_sum_ge (@fin_lift_rev n m i).val n with in_sum q q,
  { hinduction nat.not_lt_zero _ (nat.lt_of_add_lt_add_left q) },
  { apply tr_eq_of_eq_inv_tr, 
    change @sum.rec ((@fin_lift_rev n m i).val < n) ((@fin_lift_rev n m i).val ≥ n) 
                    (λ s, @tuple.append Set _ _ A B (@fin_lift_rev n m i)) _ _ _ = _, 
    rwr in_sum, change _ ▸[λ i, @tuple.append Set n m A B i] _ = _, rwr eq.inv_inv,
    have p : fin_lift_desc_rev (fin_lift_rev i) q = 
                        ap fin_lift_rev (fin_desc_lift_rev i q), from is_set.elim _ _, 
    rwr p, rwr tr_ap,
    exact apdt (λ i, (tuple.append_right A B i)⁻¹ ▸ t i) (fin_desc_lift_rev i q) }
end 

@[hott]
def fin_map.split_append {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} : 
  Π (s : Π (i : fin n), A i) (t : Π (i : fin m), B i), 
  (fin_map.split_left (fin_map.append s t) = s) × 
  (fin_map.split_right (fin_map.append s t) = t) :=
begin
  intros s t, fapply prod.mk,
  { apply eq_of_homotopy, intro i, hinduction nat.lt_sum_ge i.val n with in_sum q q,
    { change (tuple.append_left A B i) ▸ (fin_map.append s t) _ = _, 
      rwr fin_map.append_left },
    { hinduction nat.lt_irrefl _ (nat.lt_of_le_of_lt q i.is_lt) } },
  { apply eq_of_homotopy, intro i, 
    hinduction nat.lt_sum_ge (@fin_lift_rev n m i).val n with in_sum q q,
    { hinduction nat.not_lt_zero _ (nat.lt_of_add_lt_add_left q) },
    { change (tuple.append_right A B i) ▸ (fin_map.append s t) _ = _, 
      rwr fin_map.append_right } }
end

@[hott]
def fin_map.append_split {n : ℕ} {A : tuple Set.{u} n} {m : ℕ} {B : tuple Set.{u} m} :
  Π (s : Π (i : fin (n+m)), tuple.append A B i), s = 
                        fin_map.append (fin_map.split_left s) (fin_map.split_right s) :=
begin
  intro s, apply eq_of_homotopy, intro i, 
  hinduction nat.lt_sum_ge i.val n with in_sum q q,
  { change _ = @sum.rec (i.val < n) (i.val ≥ n) (λ s, @tuple.append Set _ _ A B i) _ _ _,
    rwr in_sum, hsimp, change s i = fin_lift_desc i q ▸ _, 
    exact (apdt (λ i, s i) (fin_lift_desc i q))⁻¹ },
  { change _ = @sum.rec (i.val < n) (i.val ≥ n) (λ s, @tuple.append Set _ _ A B i) _ _ _,
    rwr in_sum, hsimp, change s i = fin_lift_desc_rev i q ▸ _, 
    exact (apdt (λ i, s i) (fin_lift_desc_rev i q))⁻¹ }
end

@[hott]
def product_of_products_is_product {n : ℕ} (A : tuple Set.{u} n) (P : Set.{u})
  {m : ℕ} (B : tuple Set.{u} m) (Q : Set.{u}) : is_cons_set_tuple_product A P ->
  is_cons_set_tuple_product B Q -> is_cons_set_tuple_product (tuple.append A B) (P × Q) :=
begin 
  intros is_prod_P is_prod_Q, fapply is_cons_set_tuple_product.mk,
  { intro t, fapply prod.mk,
    { exact is_prod_P.tuple (fin_map.split_left t) },
    { exact is_prod_Q.tuple (fin_map.split_right t) } },
  { intro pq, hinduction pq with p q, fapply dpair, 
    { exact fin_map.append (is_prod_P.gens p).1 (is_prod_Q.gens q).1 },
    { rwr (fin_map.split_append _ _).1, rwr (fin_map.split_append _ _).2,
      fapply pair_eq, exact (is_prod_P.gens p).2, exact (is_prod_Q.gens q).2 } },
  { intros s t tuple_pair_eq, rwr fin_map.append_split s, rwr fin_map.append_split t,
    apply ap011 fin_map.append,
    { exact is_prod_P.free _ _ (ap prod.fst tuple_pair_eq) },
    { exact is_prod_Q.free _ _ (ap prod.snd tuple_pair_eq) } }
end

end hott