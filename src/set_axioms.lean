import hott.prop_trunc hott.init hott.types.trunc hott.homotopy.susp prop_logic

universes u v w
hott_theory

set_option pp.universes false
set_option pp.implicit false

namespace hott
open hott.is_trunc hott.trunc hott.equiv hott.is_equiv hott.sigma hott.susp

/- Should be in [init.path]. -/
notation eq `▸[`:50 P:0 `]`:0 b:50 := transport P eq b 

/- Should be in a separate section/file in the folder [types]. 
   [Zero] and [One] are equivalent to [true] and [false] in [prop_logic], but
   we want to use them without logical connotations. -/
@[hott]
inductive Zero : Type _

@[hott]
def eq_Zero : forall f₁ f₂ : Zero, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance]
def Zero_is_prop : is_prop Zero :=
  is_prop.mk eq_Zero 

@[hott]
inductive One : Type _  
| star : One

@[hott]
def eq_One : forall t₁ t₂ : One, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl One.star),
end 

@[hott, instance]
def One_is_prop : is_prop One :=
  is_prop.mk eq_One

@[hott]
inductive Two : Type _ 
| zero : Two 
| one : Two 

/- We prove that [Two] is a set using the encode-decode method presented in the
   HoTT-book, Sec.2.13. -/
@[hott, hsimp]
def code_Two : Two.{u} -> Two.{u} -> Type.{u} :=
begin
  intros t₁ t₂, 
  induction t₁,
    induction t₂, exact One, exact Zero,
    induction t₂, exact Zero, exact One,
end  

@[hott, hsimp]
def encode_Two : Π t₁ t₂ : Two, (t₁ = t₂) -> code_Two t₁ t₂ :=
  have r : Π t : Two, code_Two t t, by 
    intro t; induction t; exact One.star; exact One.star,
  assume t₁ t₂ eq, transport (λ t : Two, code_Two t₁ t) eq (r t₁)

@[hott, hsimp]
def decode_Two : Π t₁ t₂ : Two, code_Two t₁ t₂ -> (t₁ = t₂) :=
begin
  intros t₁ t₂,
  induction t₁, 
    induction t₂, intro; refl, intro f; induction f,
    induction t₂, intro f; induction f, intro; refl,     
end    

@[hott]
def Two_eq_equiv_code : ∀ t₁ t₂ : Two, (t₁ = t₂) ≃ code_Two t₁ t₂ := 
  assume t₁ t₂, 
  have z1 : code_Two Two.zero Two.one -> Zero, from λ c, c,
  have z2 : code_Two Two.one Two.zero -> Zero, from λ c, c,
  have rinv : ∀ c : code_Two t₁ t₂, (encode_Two t₁ t₂) (decode_Two t₁ t₂ c) = c, from
    assume c, 
    begin
      induction t₁, 
        induction t₂, induction c; refl, exact Zero.rec _ (z1 c),  
        induction t₂, exact Zero.rec _ (z1 c), induction c; refl, 
    end,  
  have linv : ∀ eq : t₁ = t₂, (decode_Two t₁ t₂) (encode_Two t₁ t₂ eq) = eq, from
    begin
      intro eq,
      induction eq,
      induction t₁, 
      refl, refl,
    end,    
  equiv.mk (encode_Two t₁ t₂) 
           (is_equiv.adjointify (encode_Two t₁ t₂) (decode_Two t₁ t₂) rinv linv)

@[hott, instance]
def Two_is_set : is_set Two.{u} :=
  have Two_eq_is_prop : ∀ t₁ t₂ : Two.{u}, is_prop (t₁ = t₂), from 
    assume t₁ t₂,
    have code_Two_is_prop : is_prop (code_Two t₁ t₂), from
      begin
        induction t₁, 
          induction t₂, exact One_is_prop, exact Zero_is_prop,
          induction t₂, exact Zero_is_prop, exact One_is_prop,
      end,
    is_trunc_equiv_closed_rev -1 (Two_eq_equiv_code t₁ t₂) code_Two_is_prop,
  is_trunc_succ_intro Two_eq_is_prop

@[hott]
def Two_Set : Set :=
  Set.mk Two Two_is_set  

@[hott]
def Two_is_decidable : ∀ t₁ t₂ : Two.{u}, (t₁ = t₂) ⊎ ¬ (t₁ = t₂) :=
begin 
  intros t₁ t₂, 
  induction t₁, 
    induction t₂, exact sum.inl rfl, 
                  apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
    induction t₂, apply sum.inr; intro eq; exact Zero.rec _ (encode_Two _ _ eq),
                  exact sum.inl rfl,              
end    

/- We need the criterion [refl_rel_set] to show that a type is a set. This is 
   Thm.7.2.2 in the HoTT-book. Its proof requires a lemma. -/
/- Should be in [path.lean]. -/
@[hott, hsimp]
def concat_eq_tr_eq : Π {A : Type.{u}} {a b c: A} (p : a = c) (u : b = a),
  u ⬝ p = p ▸ u :=
by intros A a b c p u; induction p; hsimp

@[hott]   
def refl_rel_set : Π {X : Type.{u}} (R : X -> X -> Type.{u}) 
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

/- Looks like a HoTT-ism but is a way to construct sets - which can be interpreted
   as subsets. Therefore it is also contained as [is_set_pred] in [subset.lean]. 
   But we want to avoid dependencies.  -/
@[hott, instance]   
def Sigma_Set_Prop_is_set (X : Set.{u}) (P : X -> trunctype.{u} -1) : 
  is_set (Σ x : X, P x) := 
have forall (x : X), is_set (P x), from 
  assume x, 
  have is_prop (P x), from trunctype.struct (P x),
  is_trunc_succ (P x) -1, 
is_trunc_sigma (λ x : X, ↥(P x)) 0    

@[hott, instance]
def fib_set_map_is_set {A B : Set.{u}} (f : A -> B) (b : B) : is_set (fiber f b) :=
  have sig_fib_is_set : is_set (Σ a : A, f a = b), from 
    let P := λ a : A, Prop.mk (f a = b) (is_prop.mk (@is_set.elim _ _ (f a) b)) in
    Sigma_Set_Prop_is_set A P,
  is_trunc_equiv_closed_rev 0 (fiber.sigma_char f b) sig_fib_is_set 

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). We postulate both as axioms, to keep track of their use, even if by 
   Lem.3.8.2, the two are equivalent. -/
@[hott]
def Choice := Π (X : Set.{u}) (A : X -> Set.{u}) 
  (P: Π x : X, A x -> trunctype.{u} -1),
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), Π x : X, P x (g x) ∥   

@[hott]
axiom AC : Choice

@[hott]
def Choice_nonempty := Π (X : Set.{u}) (Y : X -> Set.{u}), 
  (Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥ 

@[hott]
axiom AC_nonempty : Choice_nonempty

@[hott]
lemma AxChoice_equiv : Choice.{u} ↔ Choice_nonempty.{u} :=
  have imp1 : Choice.{u} -> Choice_nonempty.{u}, from 
    assume AxCh, assume X Y pi_trunc, 
    have pi_trunc_T : Π x : X, ∥ Σ y : Y x, True ∥, from 
      assume x, trunc_functor -1 (λ y : Y x, ⟨y,true.intro⟩) (pi_trunc x),
    have trunc_sigma_T : ∥ Σ (g : Π x : X, Y x), ∀ x : X, True ∥, from 
      AxCh X Y (λ x : X, λ y : Y x, True) pi_trunc_T, 
    have sigma_pi_T : (Σ (g : Π x : X, Y x), ∀ x : X, True) -> (Π x : X, Y x), from
      assume sigma_T, sigma_T.1,    
    trunc_functor -1 sigma_pi_T trunc_sigma_T,
  have imp2 : Choice_nonempty -> Choice, from 
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

/- The Law of the Excluded Middle, following the HoTT-book, (3.4.1) -/
def ExcludedMiddle := Π (A : trunctype.{u} -1), A ⊎ ¬ A

@[hott]
axiom LEM : ExcludedMiddle

/- We follow the proof of Diaconescu (HoTT-book, Thm.10.1.14) to show that the Axiom 
   of Choice (in its second version [AxChoice_nonempty]) implies the Law of the Excluded 
   Middle. 
   
   The first step is a lemma stating that the suspension (see HoTT-book, Sec.6.5) of a 
   mere proposition is a set. For its proof we use the criterion [refl_rel_set] 
   (HoTT-book, Thm.7.2.2) and construct a reflexive relation using double induction
   on [⅀ A]. This is a lot of work since [⅀ A] is a HIT, and we have to check equalities
   and equalities of equalities. -/
@[hott]
def susp_double_rec {A : Type u} {P : ⅀ A -> ⅀ A -> Type v}
  (PNN : P north north) (PNS : P north south) (PSN : P south north) 
  (PSS : P south south) (PN_m : Π a : A, PNN =[merid a] PNS)
  (PS_m : Π a : A, PSN =[merid a] PSS) 
  (P_Nm : Π a : A, PNN =[merid a; λ x : ⅀ A, P x north] PSN)
  (P_Sm : Π a : A, PNS =[merid a; λ x : ⅀ A, P x south] PSS)
  (P__m : Π a b : A, P_Nm a 
            =[merid b; λ y : ⅀ A, @susp.rec _ (P north) PNN PNS PN_m y 
                 =[merid a; λ (x : ⅀ A), P x y] susp.rec PSN PSS PS_m y] P_Sm a)
  (x y : ⅀ A) : P x y :=
begin 
  hinduction x using susp.rec,
    hinduction y using susp.rec,
      exact PNN, exact PNS, apply PN_m,
    hinduction y using susp.rec,
      exact PSN, exact PSS, apply PS_m, 
    hinduction y using susp.rec, 
      hsimp; apply P_Nm, hsimp; apply P_Sm,
      hsimp, repeat {rwr idp_inv}, repeat {rwr cast_def}, repeat {rwr idp_tr}, 
      apply P__m
end     

@[hott, hsimp]
def susp_susp_Type (A : Type u) : ⅀ A -> ⅀ A -> Type.{u+1} :=
  λ x y : ⅀ A, Type.{u}

@[hott]
def susp_of_prop_rel (A : Type u) [is_prop A] : ⅀ A -> ⅀ A -> Type.{u} :=
  assume x y,
  let P := susp_susp_Type A in
  have PN_m : Π a : A, One =[merid a; λ x : ⅀ A, P north x] A, from 
    assume a, inhabited_prop_po One A (merid a) One.star a,
  have PS_m : Π a : A, A =[merid a; λ x : ⅀ A, P south x] One, from 
    assume a, inhabited_prop_po A One (merid a) a One.star, 
  have P_Nm : Π a : A, One =[merid a; λ x : ⅀ A, P x north] A, from 
    assume a, inhabited_prop_po One A (merid a) One.star a,
  have P_Sm : Π a : A, A =[merid a; λ x : ⅀ A, P x south] One, from 
    assume a, inhabited_prop_po A One (merid a) a One.star,
  have is_prop_P_Sm : ∀ a : A, is_prop (A =[merid a; λ x : ⅀ A, P x south] One), from 
    assume a, po_is_prop (merid a),  
  have P__m : Π a b : A, P_Nm a 
     =[merid b; λ y : ⅀ A, @susp.rec _ (P north) One A PN_m y 
       =[merid a; λ (x : ⅀ A), P x y] @susp.rec _ (P south) A One PS_m y] P_Sm a, from
    assume a b, 
    @po_proofs _ _ _ (merid b) 
        (λ y : ⅀ A, @susp.rec _ (P north) One A PN_m y 
          =[merid a; λ (x : ⅀ A), P x y] @susp.rec _ (P south) A One PS_m y)
        (is_prop_P_Sm a) (P_Nm a) (P_Sm a),             
  @susp_double_rec A P One A A One PN_m PS_m P_Nm P_Sm P__m x y     

@[hott]
def susp_of_prop_rel_is_mere_rel (A : Type u) [is_prop A] : 
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

@[hott]
def susp_of_prop_rel_is_refl (A : Type u) [is_prop A] :
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

/- The next two lemmas should be in [init.pathover.lean]. -/
@[hott]
def fn_pathover_eval {A : Type u} {a b : A} (e : a = b) {P Q : A -> Type v}
  {ta : P a -> Q a} : ∀ x : P b, (e ▸ ta) x = e ▸ ta (e⁻¹ ▸ x) :=
begin hinduction e, hsimp, intro x, exact idp end  

@[hott]
def susp_of_prop_rel_id (A : Type u) [is_prop A] :
  ∀ x y : ⅀ A, susp_of_prop_rel A x y -> x = y :=
begin
  intros x y,
  hinduction x using susp.rec,
    hinduction y using susp.rec,
      intro, refl,
      intro a, exact merid a,
      apply pathover_of_tr_eq, apply eq_of_homotopy,
        intro a', rwr fn_pathover_eval, change (refl north) ⬝ merid a = merid a', 
        rwr idp_con, apply ap, apply is_prop.elim,
  hinduction y using susp.rec,
    intro a, exact (merid a)⁻¹,
    intro, refl,
    
end  

@[hott]
def susp_of_prop_is_set (A : Type u) [is_prop A] : is_set (⅀ A) := 
  (refl_rel_set (susp_of_prop_rel A) (susp_of_prop_rel_is_mere_rel A)
   (susp_of_prop_rel_is_refl A) (susp_of_prop_rel_id A)).1

@[hott] 
def AC_implies_LEM : Choice_nonempty.{u} -> ExcludedMiddle.{u} :=
  assume AC, assume A, 
  let f := λ pt : Two.{u}, @Two.rec (λ t : Two, ⅀ A) (@north A) (@south A) pt in 
  have zn : f Two.zero = north, by refl,
  have zs : f Two.one = south, by refl,
  have f_is_surj : @is_surjective Two (⅀ A) f, from 
    have PN : @image Two (⅀ A) f north, from @image.mk Two (⅀ A) f _ Two.zero zn,
    have PS : @image Two (⅀ A) f south, from @image.mk Two (⅀ A) f _ Two.one zs,
    have Pm : Π a : A, PN =[merid a; λ x : susp A, @image Two (⅀ A) f x] PS, from 
      assume a, pathover_prop_eq _ (merid a) PN PS,
    assume x, susp.rec PN PS Pm x,
  let X := Set.mk (⅀ A) (susp_of_prop_is_set A),
      Y := λ x : X, Set.mk (@fiber Two (⅀ A) f x) (@fib_set_map_is_set Two_Set X f x) in 
  have mere_g : ∥ Π x : X, @fiber Two (⅀ A) f x ∥, from AC X Y f_is_surj, 
  have g_inv_f : (Π x : X, @fiber Two (⅀ A) f x) -> 
                              (Σ (g : ⅀ A -> Two), Π (x : ⅀ A), f (g x) = x), from
    assume g, ⟨λ x : ⅀ A, (g x).1, λ x : ⅀ A, (g x).2 ⟩, 
  have g_f_dec : Π (g : ⅀ A -> Two), (g (f Two.zero) = g (f Two.one)) ⊎ 
                                          ¬ (g (f Two.zero) = g (f Two.one)), from
    assume g, Two_is_decidable (g (f Two.zero)) (g (f Two.one)),                                   
  sorry

end hott