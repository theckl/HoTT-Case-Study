import hott.prop_trunc hott.init hott.types.trunc hott.homotopy.susp prop_logic 
       sets.subset

universes u v w
hott_theory

namespace hott
open hott.is_trunc hott.trunc hott.equiv hott.is_equiv hott.sigma hott.susp hott.sum ulift
     hott.subset

set_option pp.universes true

/- Looks like a HoTT-ism but is a way to construct sets - which can be interpreted
   as subsets. Therefore it is also contained as [is_set_pred] in [subset.lean]. 
   But we want to avoid dependencies.  -/
@[hott, instance]   
def Sigma_Set_Prop_is_set (X : Set) (P : X -> Prop) : 
  is_set (Σ x : X, P x) := 
have forall (x : X), is_set (P x), from 
  assume x, 
  have is_prop (P x), from trunctype.struct (P x),
  is_trunc_succ (P x) -1, 
is_trunc_sigma (λ x : X, ↥(P x)) 0    

@[hott, instance]
def fib_set_map_is_set {A B : Set} (f : A -> B) (b : B) : is_set (fiber f b) :=
  have sig_fib_is_set : is_set (Σ a : A, f a = b), from 
    let P := λ a : A, Prop.mk (f a = b) (is_prop.mk (@is_set.elim _ _ (f a) b)) in
    Sigma_Set_Prop_is_set A P,
  is_trunc_equiv_closed_rev 0 (fiber.sigma_char f b) sig_fib_is_set 

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). We postulate both as axioms, to keep track of their use, even if by 
   Lem.3.8.2, the two are equivalent. -/
@[hott]  --[GEVE]
def Choice := Π (X : Set.{u}) (A : X -> Set.{v}) 
  (P: Π x : X, A x -> trunctype.{v} -1),
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), Π x : X, P x (g x) ∥   

@[hott]
axiom AC : Choice

@[hott]
def Choice_nonempty := Π (X : Set.{u}) (Y : X -> Set.{v}), 
  (Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥ 

@[hott]
axiom AC_nonempty : Choice_nonempty

@[hott]
def AxChoice_equiv : Choice.{u v} ↔ Choice_nonempty.{u v} :=
  have imp1 : Choice.{u v} -> Choice_nonempty.{u v}, from 
    assume AxCh, assume X Y pi_trunc, 
    have pi_trunc_T : Π x : X, ∥ Σ y : Y x, True ∥, from 
      assume x, trunc_functor -1 (λ y : Y x, ⟨y,true.intro⟩) (pi_trunc x),
    have trunc_sigma_T : ∥ Σ (g : Π x : X, Y x), ∀ x : X, True ∥, from 
      AxCh X Y (λ x : X, λ y : Y x, True) pi_trunc_T, 
    have sigma_pi_T : (Σ (g : Π x : X, Y x), ∀ x : X, True) -> (Π x : X, Y x), from
      assume sigma_T, sigma_T.1,    
    trunc_functor -1 sigma_pi_T trunc_sigma_T,
  have imp2 : Choice_nonempty.{u v} -> Choice.{u v}, from 
    assume AxCh_ne, assume X A P pi_trunc, 
    have sigma_P_is_set : Π x : X, is_set (Σ (a : A x), P x a), from 
      assume x, Sigma_Set_Prop_is_set (A x) (P x),
    let Sigma_P := λ x, Set.mk (Σ (a : A x), P x a) (sigma_P_is_set x) in 
    have trunc_pi : ∥ Π (x : X), Σ (a : A x), P x a ∥, from 
      AxCh_ne X Sigma_P pi_trunc,
    have pssp : (Π (x : X), Σ (a : A x), P x a) -> (Σ (g : Π x : X, A x), Π x : X, P x (g x)), from
      (sigma_pi_equiv_pi_sigma (λ (x : X) (a : A x), ↥(P x a)))⁻¹ᶠ,   
    trunc_functor -1 pssp trunc_pi,
  (imp1, imp2)


/- We follow the proof of Diaconescu (HoTT-book, Thm.10.1.14) to show that the Axiom 
   of Choice (in its second version [AxChoice_nonempty]) implies the Law of the Excluded 
   Middle. 
   
   The first step is a lemma stating that the suspension (see HoTT-book, Sec.6.5) of a 
   mere proposition is a set. For its proof we use the criterion [refl_rel_set] 
   (HoTT-book, Thm.7.2.2) and construct a reflexive relation using double induction
   on [⅀ A]. This is a lot of work since [⅀ A] is a HIT, and we have to check equalities
   and equalities of equalities.     

   We need the criterion [refl_rel_set] to show that a type is a set. This is 
   Thm.7.2.2 in the HoTT-book. Its proof requires a lemma. 
   Should be in [path.lean]. -/
@[hott, hsimp]
def concat_eq_tr_eq : Π {A : Type _} {a b c: A} (p : a = c) (u : b = a),
  u ⬝ p = p ▸ u :=
by intros A a b c p u; induction p; hsimp

@[hott]   
def refl_rel_set : Π {X : Type _} (R : X -> X -> Type _) 
     (mere_rel : ∀ x y, is_prop (R x y)) (refl_rel : Π x, R x x) 
     (rel_id : Π x y, R x y -> x = y), (is_set X) × (∀ x y, R x y ≃ x = y) :=
assume X R mere_rel refl_rel rel_id, 
have X_is_set : is_set X, from 
  have X_has_K : Π (x : X) (p : x = x), p = rfl, from 
    assume x p,
    have eq_tr : p ▸[λ y : X, R x y] (refl_rel x) = refl_rel x, from 
      is_prop.elim' _ _ (mere_rel x x),
    have tr_rel_id : Π {y z : X} (p : y = z) (r : R x y), 
            p ▸[λ w : X, x = w] (rel_id x y r) = rel_id x z (p ▸ r), from
      by intros x y p; induction p; intro r; hsimp,                      
    have eq_rel : rel_id x x (refl_rel x) ⬝ p = rel_id x x (refl_rel x), from 
      calc rel_id x x (refl_rel x) ⬝ p = 
                                  (p ▸[λ a : X, x = a] rel_id x x (refl_rel x)) : 
           concat_eq_tr_eq p (rel_id x x (refl_rel x))
           ... = rel_id x x (p ▸[λ y : X, R x y] refl_rel x) : 
           tr_rel_id p (refl_rel x) 
           ... = rel_id x x (refl_rel x) : by rwr eq_tr, 
    eq_idp_of_con_left eq_rel,
  have X_has_UIP : Π (x y : X) (p q : x = y), p = q, by  
    intros x y p q; induction q; exact X_has_K x p, /- This is Thm.7.2.1. -/
  have X_eq_is_prop : Π (x y : X), is_prop (x = y), from 
    assume x y, is_prop.mk (X_has_UIP x y),
  is_trunc_succ_intro X_eq_is_prop,
have rel_equiv_id : ∀ x y, R x y ≃ x = y, from 
  assume x y,
  have eq_prop : is_prop (x = y), from is_prop.mk (@is_set.elim X X_is_set x y),
  have rel_eq : R x y -> x = y, from rel_id x y,
  have eq_rel : x = y -> R x y, from assume p, p ▸[λ w : X, R x w] (refl_rel x),
  @prop_iff_equiv _ _ (mere_rel x y) eq_prop (rel_eq, eq_rel),
(X_is_set, rel_equiv_id)

/- We define the relation on [⅀ A × ⅀ A] using double induction. -/
@[hott]
def susp_of_prop_rel (A : Type _) [HA : is_prop A] : ⅀ A -> ⅀ A -> Type _ :=
let P := λ x y : ⅀ A, Type _ in
begin
  intros x y,
  hinduction x using susp.rec with a,
    hinduction y using susp.rec,
      exact One, 
      exact A, 
      exact inhabited_prop_po One A (merid a) One.star a,
    hinduction y using susp.rec,
      exact A,
      exact One,
      exact inhabited_prop_po A One (merid a) a One.star, 
    hinduction y using susp.rec with b,
      change One =[merid a; λ (x' : ↥(⅀ A)), Type _] A,
        exact inhabited_prop_po One A (merid a) One.star a,
      change A =[merid a; λ (x' : ↥(⅀ A)), Type _] One, 
        exact inhabited_prop_po A One (merid a) a One.star, 
      have is_prop_P_Sm : ∀ a : A, is_prop (A =[merid a; λ x : ⅀ A, P x south] One), from 
        begin intro a', exact po_is_prop (merid a') end, --assume a, po_is_prop (merid a),  
      exact @po_proofs _ _ _ (merid b) (λ y : ⅀ A, 
              @susp.rec _ (P north) One A (λ a : A, inhabited_prop_po One A (merid a) One.star a) y 
                  =[merid a; λ (x : ⅀ A), P x y] 
              @susp.rec _ (P south) A One (λ a : A, inhabited_prop_po A One (merid a) a One.star) y) 
                   (is_prop_P_Sm a) _ _
end  

/- The relation on [⅀ A × ⅀ A] is a mere relation. -/
@[hott]
def susp_of_prop_rel_is_mere_rel (A : Type _) [is_prop A] : 
  ∀ x y : ⅀ A, is_prop (susp_of_prop_rel A x y) :=
have NN_eq : susp_of_prop_rel A north north = One, from rfl,
have NS_eq : susp_of_prop_rel A north south = A, from rfl,
have SN_eq : susp_of_prop_rel A south north = A, from rfl,
have SS_eq : susp_of_prop_rel A south south = One, from rfl,
begin
  intros x y,  
  hinduction x using susp.rec,
    hinduction y using susp.rec, 
      rwr NN_eq, exact One_is_prop,  
      rwr NS_eq, assumption, 
      apply pathover_of_tr_eq, apply is_prop.elim,
    hinduction y using susp.rec, 
      rwr SN_eq, assumption,  
      rwr SS_eq, exact One_is_prop, 
      apply pathover_of_tr_eq, apply is_prop.elim, 
    apply pathover_of_tr_eq, apply is_prop.elim,    
end  

/- The relation on [⅀ A × ⅀ A] is a reflexive. -/
@[hott]
def susp_of_prop_rel_is_refl (A : Type _) [is_prop A] :
  Π x : ⅀ A, susp_of_prop_rel A x x :=
begin
  have NN_eq : susp_of_prop_rel A north north = One, from rfl,
  have SS_eq : susp_of_prop_rel A south south = One, from rfl,
  intro x, 
  hinduction x using susp.rec, 
    exact One.star,
    exact One.star,
    apply pathover_of_tr_eq, 
    exact @is_prop.elim _ (susp_of_prop_rel_is_mere_rel A south south) _ _,
end  

/- The next lemmas should be in [init.pathover.lean] and [init.path.lean]. -/
@[hott]
def fn_pathover_eval {A : Type u} {a b : A} (e : a = b) {P Q : A -> Type v}
  {ta : P a -> Q a} : ∀ x : P b, (e ▸ ta) x = e ▸ ta (e⁻¹ ▸ x) :=
begin hinduction e, hsimp, intro x, exact idp end  

@[hott]
def tr_eq_inv_con {A : Type u} {a b c: A} (e : a = b) (f : a = c) : e ▸[λ d, d = c] f = e⁻¹ ⬝ f :=
  begin hinduction e, apply tr_eq_of_pathover, 
                apply pathover_idp_of_eq, rwr idp_inv, rwr idp_con end

@[hott] 
def tr_fn_eq {A : Type u} {B : Type v} {a b : A} (p : a = b) {P Q : A -> B} (q : P a = Q a) :
  p ▸[λ c, P c = Q c] q = (ap P p)⁻¹ ⬝ q ⬝ (ap Q p) :=
begin 
  hinduction p, apply tr_eq_of_pathover, apply pathover_idp_of_eq, rwr ap_idp, rwr ap_idp,
  rwr idp_inv, rwr idp_con,
end  

/- Construction of identies from relations of north and of south. -/
@[hott, hsimp]
def PN_ {A : Type _} [pA : is_prop A] : 
  ∀ y : ⅀ A, susp_of_prop_rel A north y -> north = y :=
begin 
  intro y,
  hinduction y using susp.rec,
    intro, refl,
    intro a, exact merid a,
    apply pathover_of_tr_eq, apply eq_of_homotopy,
      intro a', rwr fn_pathover_eval, change (refl north) ⬝ merid a = merid a', 
      rwr idp_con, apply ap, apply is_prop.elim,
end

@[hott, hsimp]
def PS_ {A : Type _} [pA : is_prop A] : 
  ∀ y : ⅀ A, susp_of_prop_rel A south y -> south = y :=
begin
  intro y,
  hinduction y using susp.rec,      
    intro a', exact (merid a')⁻¹,
    intro, refl,
    apply pathover_of_tr_eq, apply eq_of_homotopy, intro s, rwr fn_pathover_eval, 
      change (merid ((merid a)⁻¹ ▸ s))⁻¹ ⬝ (merid a) = refl south,           
      apply inverse, apply idp_eq_inv_con, apply ap, apply @is_prop.elim _ pA _ _, 
end

/- We need to construct paths between the functions [PN_] and [PS_] over meridians and then show 
  equality of these paths. This works easily if we construct the second path as a transport of the 
  first path via a meridian, and meridians are equal. -/
@[hott]
def Q_N {A : Type _} [pA : is_prop A] (a : A) : 
  PN_ north =[merid a; λ (x' : ↥(⅀ A)), susp_of_prop_rel A x' north → x' = north] PS_ north :=
begin
  apply pathover_of_tr_eq, apply eq_of_homotopy, intro a', rwr fn_pathover_eval,
  change merid a ▸[λ x, x = north] refl north = (merid a')⁻¹, rwr tr_eq_inv_con,
  rwr con_idp, apply ap (λ a : A, (merid a)⁻¹), apply is_prop.elim
end   

@[hott]
def Q_S {A : Type _} [pA : is_prop A] (a : A) : 
  PN_ south =[merid a; λ (x' : ↥(⅀ A)), susp_of_prop_rel A x' south → x' = south] PS_ south :=
merid a▸[λ {a_1 : ↥(⅀ A)},
        PN_ a_1 =[merid a; λ (x' : ↥(⅀ A)), susp_of_prop_rel A x' a_1 → x' = a_1] PS_ a_1]Q_N a  

@[hott]
def susp_of_prop_rel_id (A : Type _) [pA : is_prop A] :
  ∀ x y : ⅀ A, susp_of_prop_rel A x y -> x = y :=
let R := λ x y : ⅀ A, susp_of_prop_rel A x y in 
begin
  intros x y,
  hinduction x using susp.rec,
    exact PN_ y,
    exact PS_ y,
    hinduction y using susp.rec with a₁,
      exact Q_N a,
      exact Q_S a, 
      have merid_eq : merid a₁ = merid a, from 
        begin apply ap, apply is_prop.elim end, 
      apply pathover_of_tr_eq, rwr merid_eq
end  

@[hott]
def susp_of_prop_is_set (A : Type _) [is_prop A] : is_set (⅀ A) := 
  (refl_rel_set (susp_of_prop_rel A) (susp_of_prop_rel_is_mere_rel A)
   (susp_of_prop_rel_is_refl A) (susp_of_prop_rel_id A)).1

/- Using the second part of Thm.7.2.2 = [refl_rel_set] we can show a corollary: -/
@[hott]
def merid_equiv_A (A : Type _) [is_prop A] : (@north A = south) ≃ A :=
  have A_equiv_merid : A ≃ (@north A = south), from 
    (refl_rel_set (susp_of_prop_rel A) (susp_of_prop_rel_is_mere_rel A)
                   (susp_of_prop_rel_is_refl A) (susp_of_prop_rel_id A)).2 north south,
  A_equiv_merid⁻¹ᵉ   

/- This is a simplified version of closedness under equivalences for decidability. -/
@[hott]
def iff_LEM_LEM {A B : Type u} : (A ↔ B) -> (A ⊎ ¬ A) -> (B ⊎ ¬ B) :=
  assume AB_iff, assume A_dec, 
  begin
    hinduction A_dec with a na, 
      exact sum.inl (AB_iff.1 a),
      apply sum.inr, assume b, exact empty.elim (na (AB_iff.2 b)) 
  end  

/- Diaconescu's Theorem, HoTT-book, [Thm.10.1.14] -/
@[hott] 
def AC_implies_LEM : Choice_nonempty.{u} -> ExcludedMiddle.{u} :=
  assume AC, assume A, 
  let f := @Two.rec (λ t : Two.{u}, ⅀ A) (@north A) (@south A) in 
  have zn : f Two.zero = north, by refl,
  have zs : f Two.one = south, by refl,
  have f_is_surj : @is_surjective Two (⅀ A) f, from 
    have PN : @image Two (⅀ A) f north, from @image.mk Two (⅀ A) f _ Two.zero zn,
    have PS : @image Two (⅀ A) f south, from @image.mk Two (⅀ A) f _ Two.one zs,
    have Pm : Π a : A, PN =[merid a; λ x : susp A, @image Two (⅀ A) f x] PS, from 
      assume a, pathover_prop_eq _ (merid a) PN PS,
    assume x, susp.rec PN PS Pm x,
  let X := Set.mk (⅀ A) (susp_of_prop_is_set.{u u} A),
      Y := λ x : X, Set.mk (@fiber Two (⅀ A) f x) (@fib_set_map_is_set Two_Set X f x) in 
  have mere_g : ∥ Π x : X, @fiber Two (⅀ A) f x ∥, from AC X Y f_is_surj, 
  have g_inv_f : (Π x : X, @fiber Two (⅀ A) f x) -> 
                              (Σ (g : ⅀ A -> Two), Π (x : ⅀ A), f (g x) = x), from
    assume g, ⟨λ x : ⅀ A, (g x).1, λ x : ⅀ A, (g x).2 ⟩, 
  have g_f_dec : Π (g : ⅀ A -> Two), (g (f Two.zero) = g (f Two.one)) ⊎ 
                                          ¬ (g (f Two.zero) = g (f Two.one)), from                                          
    assume g, Two_is_decidable (g (f Two.zero)) (g (f Two.one)),  
  have f_dec : (Π x : X, @fiber Two (⅀ A) f x) -> (f Two.zero = f Two.one) ⊎ 
                                                  ¬ (f Two.zero = f Two.one), from 
    assume sect_f, let g := (g_inv_f sect_f).1, gf_dec := g_f_dec g in 
    have g_inj : ∀ x y : ⅀ A, g x = g y -> x = y, from 
      assume x y g_eq, 
      have fg_eq : f (g x) = f (g y), by rwr g_eq,
      ((g_inv_f sect_f).2 x)⁻¹ ⬝ fg_eq ⬝ ((g_inv_f sect_f).2 y), 
    have gf01_f01_eq : g (f Two.zero) = g (f Two.one) -> f Two.zero = f Two.one, from 
      assume gf_eq, 
      have fgf_eq : f (g (f Two.zero)) = f (g (f Two.one)), by rwr gf_eq,
      ((g_inv_f sect_f).2 (f Two.zero))⁻¹ ⬝ fgf_eq ⬝ ((g_inv_f sect_f).2 (f Two.one)),
    have f01_gf01_eq : f Two.zero = f Two.one -> g (f Two.zero) = g (f Two.one), from
      begin intro f_eq, rwr f_eq end,     
    iff_LEM_LEM ⟨gf01_f01_eq, f01_gf01_eq⟩ (g_f_dec g),  
  have A_dec :  (Π x : X, @fiber Two (⅀ A) f x) -> A ⊎ ¬ A, from 
    assume sect_f, 
    have NS_eq_dec : (@north A = south) ⊎ ¬ (@north A = south), from
      begin rwr zn⁻¹, rwr zs⁻¹, exact f_dec sect_f end,
    have NS_eq_iff_A : (@north A = south) ↔ A, from 
      ⟨merid_equiv_A.{u u} A, (merid_equiv_A.{u u} A)⁻¹ᶠ⟩,
    iff_LEM_LEM NS_eq_iff_A NS_eq_dec,                                                                                
  have trunc_LEM : ∥ A ⊎ ¬ A ∥, from trunc_functor -1 A_dec mere_g,
  @untrunc_of_is_trunc _ _ is_prop_LEM trunc_LEM

/- We deduce LEM (decidability) for the element relation of a set from general LEM, 
   and conversely, we derive LEM from decidability of the element relation of an 
   inhabited set, namely `One_Set`. -/
@[hott, instance]
def has_dec_elem_of_LEM (A : Set): has_dec_elem A := 
  begin apply has_dec_elem.mk, intros a S, exact LEM (a ∈ S) end

@[hott]
def LEM_of_has_dec_elem : has_dec_elem One_Set -> ExcludedMiddle :=
begin
  intros H P, let S : Subset One_Set := λ s, P, exact @has_dec_elem.dec_el _ H One.star S
end

end hott