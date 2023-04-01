import hott.init hott.hit.trunc hott.types.trunc hott.types.nat.order init2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat

/- Properties of the product of two types -/
@[hott]
def all_prod_all {I J : Type _} (F : I -> J -> Type _) : 
  (∀ p : I × J, F p.1 p.2) -> ∀ (i : I) (j : J), F i j :=
assume all_prod i j, all_prod ⟨i,j⟩  

/- An extended elimination principle for truncations -/
@[hott]
def trunc.elim2 {n : ℕ₋₂} {A : Type _} {B : Type _} {P : Type _} [Pt : is_trunc n P] : 
  (A → B -> P) → trunc n A → trunc n B -> P :=
begin intros f tA tB, exact untrunc_of_is_trunc (trunc_functor2 f tA tB) end  

/- Some useful facts on identities of Σ-types and pairs. -/
@[hott]
def sigma_Prop_eq {A : Type _} {B : Π a : A, Prop} (s₁ s₂ : Σ (a : A), B a) : 
  s₁.1 = s₂.1 -> s₁ = s₂ :=
begin 
  intro p, fapply sigma.sigma_eq, 
  exact p, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end  

@[hott]
def pair_eq {A B : Type _} : Π (c₁ c₂ : A × B), c₁.1 = c₂.1 -> c₁.2 = c₂.2 -> c₁ = c₂ :=
begin 
  intros c₁ c₂, 
  hinduction c₁ with c₁_1 c₁_2, hinduction c₂ with c₂_1 c₂_2, hsimp,
  intros q₁ q₂, apply ap011 pair q₁ q₂ 
end

@[hott]
def sigma2_eq' {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A}
  {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} : 
  Π (p : a₁ = a₂) (q : b₁ = b₂) (r : (ap011 C p q) ▸[id] c₁ = c₂), 
  dpair a₁ (dpair b₁ c₁) = ⟨a₂, ⟨b₂, c₂⟩⟩ :=
begin
  intros p q r, hinduction p, hinduction q, 
  fapply sigma.sigma_eq, refl, apply pathover_idp_of_eq, 
  fapply sigma.sigma_eq, refl, apply pathover_idp_of_eq, exact r
end  

/- The decode-encode technique for sums; it is contained in [types.sum] from the HoTT3 
   library, but this file does not compile. -/
@[hott, reducible, hsimp] 
def sum_code {A : Type.{u}} {B : Type.{v}} : A ⊎ B → A ⊎ B → Type (max u v) :=
  begin
    intros x y, induction x with a b; induction y with a' b',
    exact ulift.{(max u v) u} (a = a'), exact ulift empty,
    exact ulift empty, exact @ulift.{(max u v) v} (b = b')
  end   

@[hott] 
def sum_decode {A : Type.{u}} {B : Type.{v}} : 
  Π (z z' : A ⊎ B), sum_code z z' → z = z' :=
  begin
    intros z z', induction z with a b; induction z' with a' b',
    exact λ c, ap sum.inl (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, ap sum.inr (ulift.down c)
  end

@[hott] 
def sum_encode {A : Type.{u}} {B : Type.{v}} {z z' : A ⊎ B} (p : z = z') : sum_code z z' :=
  by induction p; induction z; exact ulift.up idp

@[hott] 
def empty_of_inl_eq_inr {A : Type.{u}} {B : Type.{v}} {a : A} {b : B} 
  (p : sum.inl a = sum.inr b) : empty :=
ulift.down (sum_encode p)

@[hott] 
def empty_of_inr_eq_inl {A : Type.{u}} {B : Type.{v}} {a : A} {b : B}
  (p : sum.inr b = sum.inl a) : empty := 
ulift.down (sum_encode p)

@[hott, instance] 
def decidable_eq_sum (A B : Type _)
    [HA : hott.decidable_eq A] [HB : hott.decidable_eq B] :
    hott.decidable_eq (A ⊎ B) :=
  begin
    intros v v', induction v with a b; induction v' with a' b',
    { hinduction HA a a',
      { exact decidable.inl (ap sum.inl a_1) },
      { apply decidable.inr, intro p, apply a_1, exact ulift.down (sum_encode p) }},
    { apply decidable.inr, intro p, apply empty_of_inl_eq_inr p },
    { apply decidable.inr, intro p, apply empty_of_inr_eq_inl p },
    { hinduction HB b b',
      { exact decidable.inl (ap sum.inr a) },
      { apply decidable.inr, intro p, apply a, exact ulift.down (sum_encode p) }},
  end

@[hott] 
def sum_eq_equiv {A : Type.{u}} {B : Type.{v}} {z z' : A ⊎ B} : (z = z') ≃ sum_code z z' :=
  begin
    fapply equiv.MK, apply sum_encode, apply sum_decode,
    { induction z with a b; induction z' with a' b';
       intro b; induction b with b; induction b; reflexivity },
    { intro p, induction p, induction z; refl  }
  end

@[hott] def sum.mem_cases {A : Type.{u}} {B : Type.{v}} (z : A ⊎ B) : 
  (Σ a, z = sum.inl a) ⊎ (Σ b, z = sum.inr b) :=
begin
  induction z with a b,
  exact sum.inl ⟨a, idp⟩, exact sum.inr ⟨b, idp⟩
end

/- The injectivity of a map of types is only useful if it also implies relations between
   equalities of objects of domain and codomain, in particular that `rfl` is mapped to 
   `rfl`. For sets, this is automatic and shown in [sets.basic] -/
@[hott, class]
def is_injective {A : Type u} {B : Type v} (f : B -> A) := 
  forall b1 b2 : B, is_equiv (λ p : b1 = b2, ap f p)

@[hott]
def inj_imp {A : Type u} {B : Type v} {f : B -> A} (inj : is_injective f) :  
  ∀ b1 b2 : B, f b1 = f b2 -> b1 = b2 :=
begin intros b1 b2, exact (inj b1 b2).inv end  

@[hott]
def inj_idp {A : Type u} {B : Type v} {f : B -> A} [inj : is_injective f] :  
  ∀ b : B, inj_imp inj b b idp = idp :=
begin 
  intro b, 
  change @is_equiv.inv _ _ (λ p : b = b, ap f p) (inj b b) (@idp _ (f b)) = idp, 
  have H : (λ p : b = b, ap f p) idp = idp, from rfl,
  rwr <- H, rwr @is_equiv.left_inv _ _ (λ p : b = b, ap f p) (inj b b) (@idp _ b)
end 

/- Maps that are equivalences allow to exchange types of arguments in dependent 
   functions. -/
@[hott]
def equiv_arg_exchange {A : Type _} {B : Type _} {f : A -> B} (H : is_equiv f) 
  {C : B -> Type _} : (∀ a : A, C (f a)) -> (∀ b : B, C b) :=
begin intros g b, rwr <- is_equiv.right_inv f b, exact g (f⁻¹ᶠ b) end     

/- Inequalities of natural numbers in the core are non-HoTT propositions, so procedures
   using them need to be rewritten.  -/
@[hott, hsimp] 
def list_nth_le {α : Type _} : Π (l : list α) (n), n < l.length → α
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := a
| (a :: l) (n+1) h := list_nth_le l n (le_of_succ_le_succ h)

/- Further factes on lists -/
@[hott, hsimp]
def list_map_size_eq {A B : Type _} (f : A -> B) (l : list A) : 
  list.length (list.map f l) = list.length l :=
begin hinduction l, refl, hsimp, rwr ih end  

/- We use Egbert Rijke's insight that the main tool to deal with identity types in 
   HoTT is the Structure Identity Principle for Σ-types [Rijke-Book, Thm.11.6.2]. 
   It is the dependent version of the Fundamental Theorem of identity types
   [Thm.11.2.2] which characterizes the identity types of a type by identity
   systems which are type families with the same inductive properties as identity: 
   The fibers of such a type family are equivalent to the identity types if the 
   total space of the type family is contractible. See also [HoTT-Book, Ch.5.8]. -/
@[hott]
structure ppred {A : Type _} (a₀ : A) := 
  (fam : A -> Type _)
  (base : fam a₀)

@[hott]
def id_ppred {A : Type _} (a₀ : A) : ppred a₀ :=
  @ppred.mk A a₀ (λ a : A, a₀ = a) (idpath a₀) 

@[hott] 
structure ppmap {A : Type _} {a₀ : A} (R S : ppred a₀) := 
  (fam_map : Π (a : A), R.fam a -> S.fam a)
  (base_map : fam_map a₀ R.base = S.base) 

@[hott]
def is_id_system {A : Type _} {a₀ : A} (R : ppred a₀) := 
  Π (D : Π (a : A), R.fam a -> Type w) (d : D a₀ R.base),
      Σ (f : Π (a : A) (r : R.fam a), D a r), (f a₀ R.base = d) 

@[hott]
def id_type_fam_is_id_sys {A : Type _} {a₀ : A} : is_id_system (id_ppred a₀) :=
begin 
  intros D d, fapply dpair, 
  { intros a p, hinduction p, exact d },
  { refl }
end

@[hott]
def is_prop_is_id_sys {A : Type _} {a₀ : A} (R : ppred a₀) :
  is_prop (is_id_system R) :=
begin
  fapply is_prop.mk, intros is_id_sys_R is_id_sys_R',
  fapply eq_of_homotopy2, intros D d, 
  let D_eq := λ a r, (is_id_sys_R D d).1 a r = (is_id_sys_R' D d).1 a r,
  let d_eq := (is_id_sys_R D d).2 ⬝ (is_id_sys_R' D d).2⁻¹,                                     
  fapply sigma.sigma_eq, 
  { fapply eq_of_homotopy2, intros a r,
    exact (is_id_sys_R D_eq d_eq).1 a r },
  { apply @po_of_po_apd100 _ _ D _ _ (λ d' : D a₀ R.2, d' = d), 
    let H : (is_id_sys_R D d).1 ~2 (is_id_sys_R' D d).1 
          := λ (a : A) (r : R.fam a), (is_id_sys_R D_eq d_eq).1 a r,
    change _ =[apd100 (eq_of_homotopy2 H) a₀ R.base] _,
    rwr apd100_eq_of_hty2_inv H a₀ R.base, apply eq_con_po_eq,
    have q : (is_id_sys_R D_eq d_eq).1 a₀ R.base = d_eq, from
      (is_id_sys_R D_eq d_eq).2,      
    have p : H a₀ R.base = d_eq, by 
      change (is_id_sys_R _ _).1 a₀ R.base = _; rwr q,
    rwr p, hsimp }
end  

@[hott]
structure id_system {A : Type _} (a₀ : A) := 
  (ppred : ppred a₀) 
  (is_id_sys : is_id_system ppred)

/- We split up the implications between the properties of the Fundamental 
   Theorem of Identity as in the proof of [Rijke-Book, Thm.11.2.2].
   The properties are all propositions, hence equivalent, but this 
   seems not needed in the applications. -/
@[hott]
def tot_space_contr_id_sys {A : Type _} {a₀ : A} (R : ppred a₀) : 
  is_contr (Σ (a : A), R.fam a) -> is_id_system R :=
begin 
  intros contr D d, 
  let D' : (Σ (a : A), R.fam a) -> Type _ := λ (ar : Σ (a : A), R.fam a), D ar.1 ar.2,
  have p : Π (u : Σ (a : A), R.fam a), u = ⟨a₀, R.base⟩, from 
    assume u, @eq_of_is_contr _ contr _ _,
  have q : p ⟨a₀, R.base⟩ = idp, from @prop_eq_of_is_contr _ contr _ _ _ _,  
  fapply dpair, 
  { exact λ (a : A) (r : R.fam a), (p ⟨a, r⟩)⁻¹ ▸[D'] d },
  { apply inv_tr_eq_of_eq_tr, rwr q }
end  

@[hott]
def id_sys_tot_space_contr {A : Type _} {a₀ : A} (R : ppred a₀) : 
  is_id_system R -> is_contr (Σ (a : A), R.1 a) :=
begin 
  intro is_id_sys_R, fapply is_contr.mk,
  { exact ⟨a₀, R.base⟩ },
  { let D : Π (a : A), R.fam a -> Type _ := λ a r, 
                            @dpair A R.fam a₀ R.base = ⟨a, r⟩, 
    intro dp, hinduction dp with a r, 
    exact (is_id_sys_R D idp).1 a r }
end

/- We need some facts on families of equivalences, see [Rijke-Book, 11.1]. -/
@[hott] --[Rijke-Book, Thm.11.1.3.(i)=>(ii)] = [HoTT-Book, Thm.4.7.7]
def fam_eqv_tot_map_eqv {A : Type _} {B C : A -> Type _} 
  (f : Π a : A, B a -> C a) : 
  (Π a : A, is_equiv (f a)) -> is_equiv (sigma.total f) :=
λ fib_eqv, @is_equiv_total_of_is_fiberwise_equiv _ _ _ f fib_eqv

@[hott] --[Rijke-Book, Thm.11.1.3.(ii)=>(i)] = [HoTT-Book, Thm.4.7.7]
def tot_map_eqv_fam_eqv {A : Type _} {B C : A -> Type _} 
  (f : Π a : A, B a -> C a) : 
  is_equiv (sigma.total f) -> (Π a : A, is_equiv (f a)) :=
λ tot_eqv, @is_fiberwise_equiv_of_is_equiv_total _ _ _ f tot_eqv 

/- Now we can show the second pair of implications in [Rijke-Book, Thm.11.2.2]. 
   In particular, we can apply them to the canonical maps from the identity
   pointed predicate to arbitrary pointed predicates. -/
@[hott]
def can_ppmap {A : Type _} {a₀ : A} (R : ppred a₀) : 
  ppmap (id_ppred a₀) R :=
⟨λ (a : A) (p : a₀ = a), p ▸[λ a : A, R.fam a] R.base, idp⟩  

@[hott]
def ppmap_id_eqv_tot_space_contr {A : Type _} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), (Π (a : A), is_equiv (f.fam_map a)) ->
  is_contr (Σ (a : A), R.fam a) := 
begin
  intros f f_eqv, 
  have F : (Σ (a : A), a₀ = a) ≃ (Σ (a : A), R.fam a), from
    equiv.mk (sigma.total f.fam_map) (fam_eqv_tot_map_eqv f.fam_map f_eqv),
  exact is_trunc_equiv_closed -2 F (is_contr_tot_peq a₀)  
end

@[hott]
def tot_space_contr_ppmap_id_eqv {A : Type _} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), is_contr (Σ (a : A), R.fam a) -> 
  Π (a : A), is_equiv (f.fam_map a) := 
begin
  intros f contr_tot_R, apply tot_map_eqv_fam_eqv, 
  apply @is_equiv_of_is_contr _ _ (is_contr_tot_peq a₀) contr_tot_R
end

/- In HoTT3, types with structures are usually defined as `structure`, 
   not Σ-types. Therefore, we need to provide equivalences of structures 
   with Σ-types before we can apply the Structure Identity Principle 
   on types with structure. The proof follows that of [Rijke-Book, Thm.11.6.2], 
   splitting up the Fundamental Identity Theorem for Σ-Types into 
   checks for pointed predicates over objects of the Σ-type with 
   fixed first component and over objects of the first component. -/
@[hott]
structure dep_ppred {A : Type _} (a₀ : A) {B : A -> Type _} (b₀ : B a₀) :=
  (ppred_fst : ppred a₀)
  (dep_fam : Π (a : A), B a -> ppred_fst.fam a -> Type _) 
  (dep_base : dep_fam a₀ b₀ ppred_fst.base) 

@[hott]
def is_dep_id_system {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) := 
is_id_system (@ppred.mk _ b₀ (λ (b : B a₀), 
               R.dep_fam a₀ b R.ppred_fst.base) R.dep_base)  

@[hott]
structure dep_id_system {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} :=
(dep_ppred : dep_ppred a₀ b₀)
(id_sys_fst : is_id_system dep_ppred.ppred_fst)  
(is_dep_id_sys : is_dep_id_system dep_ppred)

/- We only need to show one equivalence between characterizations of 
   the identities in Σ-Types and identities of objects of the Σ-type 
   with fixed first component: the contractibility of the total space
   of the pairs with fixed first component and the contractibility of 
   the total space of the associated pointed predicate on the Σ-type. 
   
   The other equivalences are consequences of the equivalences in the 
   Fundamental Identity Theorem: We just include that dependent 
   identity systems give rise to identity systems on the Σ-type and
   vice versa, and state the criterion to produce equivalences from
   contractibility. -/
@[hott]
def struct_id_contr_eqv {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) : 
  is_contr (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base) ↔
  is_contr (Σ (dp : Σ (a : A), B a), 
            Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) :=
begin
  have eqv₁ : (Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base) ≃
              (Σ (dp : Σ (a : A), R.ppred_fst.fam a), 
                 Σ (b : B dp.1), R.dep_fam dp.1 b dp.2), from 
  let Df := λ (a : A) (c : R.ppred_fst.fam a), 
             (Σ (b : B a), R.dep_fam a b c) -> 
                Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base,
      df := λ dp : Σ (b : B a₀), 
                          R.dep_fam a₀ b R.ppred_fst.base, dp,
      fp := id_sys_fst Df df in
  let D_eq := λ (a : A) (c : R.ppred_fst.fam a), 
        Π (dpf : Σ (b : B a), R.dep_fam a b c),
           @dpair _ (λ (dp : Σ (a : A), R.ppred_fst.fam a), 
        Σ (b : B dp.1), R.dep_fam dp.1 b dp.2) (dpair a c) dpf =
           ⟨⟨a₀, R.ppred_fst.base⟩, fp.1 a c dpf⟩,
      d_eq := λ (dpf : Σ (b : B a₀), R.dep_fam a₀ b R.ppred_fst.base),
                (ap (@dpair _ (λ (dp : Σ (a : A), R.ppred_fst.fam a), 
        Σ (b : B dp.1), R.dep_fam dp.1 b dp.2) ⟨a₀, R.ppred_fst.base⟩) 
                (ap10 fp.2 dpf))⁻¹,
      f_eq := id_sys_fst D_eq d_eq in               
  begin  
    fapply equiv.mk,
    { intro dpB, exact ⟨⟨a₀, R.ppred_fst.base⟩, dpB⟩ },
    { fapply adjointify, 
      { intro dpR1, exact fp.1 dpR1.1.1 dpR1.1.2 dpR1.2 },
      { intro ptR, hinduction ptR with ptd ptB, 
        hinduction ptd with a ba, 
        hinduction ptB with b ptR, rwr <- f_eq.1 a ba },
      { intro ptB, hinduction ptB with b bR, hsimp, 
        rwr ap10 fp.2 ⟨b, bR⟩ } }
  end,
  have eqv₂ : (Σ (dp : Σ (a : A), R.ppred_fst.fam a), 
                 Σ (y : B dp.1), R.dep_fam dp.1 y dp.2) ≃
         (Σ (dp : Σ (a : A), B a), 
            Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c), from
  begin
    fapply equiv.mk,
    { intro tup, exact ⟨⟨tup.1.1, tup.2.1⟩, ⟨tup.1.2, tup.2.2⟩⟩ },
    { fapply adjointify, 
      { intro tup, exact ⟨⟨tup.1.1, tup.2.1⟩, ⟨tup.1.2, tup.2.2⟩⟩ },
      { intro tup, hsimp, hinduction tup with tup₁ tup₂, 
        hinduction tup₁ with a c, hinduction tup₂ with b d, hsimp },
      { intro tup, hsimp, hinduction tup with tup₁ tup₂, 
        hinduction tup₁ with a b, hinduction tup₂ with c d, hsimp } }
  end,               
  apply pair, 
  { intro contr₁, 
    exact is_trunc_equiv_closed -2 (eqv₁ ⬝e eqv₂) contr₁ },
  { intro contr₂, 
    exact is_trunc_equiv_closed_rev -2 (eqv₁ ⬝e eqv₂) contr₂ }
end    

@[hott]
def struct_id_dep_id_sys_eqv {A : Type _} {a₀ : A} {B : A -> Type _} 
  {b₀ : B a₀} (R : dep_ppred a₀ b₀) 
  (id_sys_fst : is_id_system R.ppred_fst) : (is_dep_id_system R) ↔
  (is_id_system (@ppred.mk (Σ (a : A), B a) ⟨a₀, b₀⟩ 
    (λ dp, Σ (c : R.ppred_fst.fam dp.1), R.dep_fam dp.1 dp.2 c) 
    ⟨R.ppred_fst.base, R.dep_base⟩)) :=
begin
  apply pair, 
  { intro dep_id_sys, apply tot_space_contr_id_sys,
    apply (struct_id_contr_eqv R id_sys_fst).1, 
    exact id_sys_tot_space_contr (@ppred.mk _ b₀ (λ (b : B a₀), 
      R.dep_fam a₀ b R.ppred_fst.base) R.dep_base) dep_id_sys },
  { intro id_sys, apply tot_space_contr_id_sys, 
    apply (struct_id_contr_eqv R id_sys_fst).2, 
    exact id_sys_tot_space_contr _ id_sys }
end    

@[hott]
def struct_id_char_of_contr {A : Type _} {a₀ : A} {B : A -> Type _} 
  (b₀ : B a₀) (D : dep_ppred a₀ b₀) : 
  is_contr (Σ (a : A), D.ppred_fst.fam a) -> 
  is_contr (Σ (b : B a₀), D.dep_fam a₀ b D.ppred_fst.base) ->
  Π (ab : Σ (a : A), B a), (dpair a₀ b₀ = ab) ≃ 
       Σ (c : D.ppred_fst.fam ab.1), D.dep_fam ab.1 ab.2 c :=
begin
  intros is_contr_fst is_contr_dep ab, fapply equiv.mk,
  let R := @ppred.mk _ (dpair a₀ b₀) 
              (λ ab, Σ (c : D.ppred_fst.fam ab.fst), 
                            D.dep_fam ab.fst ab.snd c) 
              ⟨D.ppred_fst.base, D.dep_base⟩,
  { exact (can_ppmap R).fam_map ab },
  { apply tot_space_contr_ppmap_id_eqv, hsimp,
    have id_sys_fst : is_id_system D.ppred_fst, from 
      tot_space_contr_id_sys D.ppred_fst is_contr_fst, 
    apply (struct_id_contr_eqv D id_sys_fst).1 is_contr_dep }
end 

end hott