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
def ppred {A : Type _} (a₀ : A) := Σ (R : A -> Type v), R a₀

@[hott]
def id_ppred {A : Type _} (a₀ : A) : ppred a₀ :=
  ⟨λ a, a₀ = a, refl a₀⟩

@[hott] 
def ppmap {A : Type _} {a₀ : A} (R S : ppred a₀) := 
  Σ (g : Π (a : A), R.1 a -> S.1 a), g a₀ R.2 = S.2 

@[hott]
def ppmap_id {A : Type _} {a₀ : A} (R : ppred a₀) : ppmap R R :=
  ⟨λ (a : A) (r : R.1 a), r, refl R.2⟩    

@[hott]
def ppmap_comp {A : Type _} {a₀ : A} {R S T : ppred a₀} (f : ppmap R S) (g : ppmap S T) :
  ppmap R T :=
⟨λ (a : A) (r : R.1 a), g.1 a (f.1 a r), f.2⁻¹ ▸[λ s : S.1 a₀, g.1 a₀ s = T.2] g.2⟩  

@[hott]
def is_id_system {A : Type _} {a₀ : A} (R : ppred a₀) := 
  Π (D : Π (a : A), R.1 a -> Type w) (d : D a₀ R.2),
                      Σ (f : Π (a : A) (r : R.1 a), D a r), (f a₀ R.2 = d) 

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
          := λ (a : A) (r : R.1 a), (is_id_sys_R D_eq d_eq).1 a r,
    change _ =[apd100 (eq_of_homotopy2 H) a₀ R.2] _,
    rwr apd100_eq_of_hty2_inv H a₀ R.2, apply eq_con_po_eq,
    have q : (is_id_sys_R D_eq d_eq).1 a₀ R.2 = d_eq, from
      (is_id_sys_R D_eq d_eq).2,      
    have p : H a₀ R.2 = d_eq, by 
      change (is_id_sys_R _ _).1 a₀ R.2 = _; rwr q,
    rwr p, hsimp }
end  

@[hott]
def id_system {A : Type u} {a₀ : A} := Σ (R : ppred a₀), is_id_system R

/- We split up the implications between the properties of the Fundamental 
   Theorem of Identity as in the proof of [Rijke-Book, Thm.11.2.2].
   The properties are all propositions, hence equivalent, but this 
   seems not needed in the applications. -/
@[hott]
def tot_space_contr_id_sys {A : Type u} {a₀ : A} (R : ppred a₀) : 
  is_contr (Σ (a : A), R.1 a) -> is_id_system R :=
begin 
  intros contr D d, 
  let D' : (Σ (a : A), R.1 a) -> Type _ := λ (ar : Σ (a : A), R.1 a), D ar.1 ar.2,
  have p : Π (u : Σ (a : A), R.1 a), u = ⟨a₀, R.2⟩, from 
    assume u, @eq_of_is_contr _ contr _ _,
  have q : p ⟨a₀, R.2⟩ = idp, from @prop_eq_of_is_contr _ contr _ _ _ _,  
  fapply dpair, 
  { exact λ (a : A) (r : R.1 a), (p ⟨a, r⟩)⁻¹ ▸[D'] d },
  { apply inv_tr_eq_of_eq_tr, rwr q }
end  

@[hott]
def id_sys_tot_space_contr {A : Type u} {a₀ : A} (R : ppred a₀) : 
  is_id_system R -> is_contr (Σ (a : A), R.1 a) :=
begin 
  intro is_id_sys_R, fapply is_contr.mk,
  { exact ⟨a₀, R.2⟩ },
  { let D : Π (a : A), R.1 a -> Type _ := λ a r, 
                                  @dpair A R.1 a₀ R.snd = ⟨a, r⟩, 
    intro dp, hinduction dp with a r, 
    exact (is_id_sys_R D idp).1 a r }
end

@[hott]
def ppmap_id_eqv_tot_space_contr {A : Type u} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), (Π (a : A), is_equiv (f.1 a)) ->
  is_contr (Σ (a : A), R.1 a) := 
begin
  intros f f_eqv, fapply is_contr.mk,
  { exact ⟨a₀, R.2⟩ },
  { intro dp, hinduction dp with a r, sorry }
end

@[hott]
def tot_space_contr_ppmap_id_eqv {A : Type u} {a₀ : A} (R : ppred a₀) : 
  Π (f : ppmap (id_ppred a₀) R), is_contr (Σ (a : A), R.1 a) -> 
  Π (a : A), is_equiv (f.1 a) := 
sorry

@[hott]
def id_sys_ppmap_contr {A : Type u} {a₀ : A} (R : ppred a₀) : is_id_system R -> 
  Π (S : ppred a₀), is_contr (ppmap R S) :=
begin
  intros idsys S, 
  let C := λ (a : A) (r : R.1 a), S.1 a, let map : ppmap R S := idsys C S.2, 
  have H : is_prop (ppmap R S), from 
  begin
    apply is_prop.mk, intros m₁ m₂, hinduction m₁ with f fᵣ, hinduction m₂ with g gᵣ,
    let D := λ (a : A) (r : R.1 a), f a r = g a r, let d := fᵣ ⬝ (gᵣ)⁻¹,
    let h := idsys D d, fapply sigma.sigma_eq,
    { apply eq_of_homotopy2, exact h.1 },
    { apply @po_of_po_apd100 A R.1 (λ a r, S.1 a) a₀ R.2 (λ c : S.1 a₀, c = S.2) _ _ 
                             (eq_of_homotopy2 h.1) fᵣ gᵣ,
      have q : apd100 (eq_of_homotopy2 h.1) = h.1, by  
        apply (funext.is_equiv_apd100 f g).right_inv,                      
      rwr q, let q' : h.1 a₀ R.2 = d := h.2, apply pathover_of_tr_eq, rwr q', 
      rwr id_tr_eq_id_inv_con, rwr con_inv, rwr eq.inv_inv, rwr con.assoc, rwr con.left_inv }
  end,
  exact @is_contr_of_inhabited_prop _ H map
end    

@[hott]
def ppmap_contr_id_equiv {A : Type u} {a₀ : A} (R : ppred a₀) :
  (Π (S : ppred a₀), is_contr (ppmap R S)) -> 
                    Π a : A, is_equiv (λ p : a₀ = a, p ▸[λ b : A, R.1 b] R.2) :=
begin 
  intro ppred_contr, let S : ppred a₀ := ⟨λ a, a₀ = a, refl a₀⟩, 
  let map_SR : ppmap S R := ⟨λ (a : A) (p : a₀ = a), p ▸[λ b, R.1 b] R.2, idp_tr R.2⟩, 
  let map_RS : ppmap R S := center' (ppred_contr S),
  let map_RR : ppmap R R := ppmap_comp map_RS map_SR, 
  have p_R : map_RR = ppmap_id R, from @eq_of_is_contr _ (ppred_contr R) _ _,
  let map_SS : ppmap S S := ppmap_comp map_SR map_RS,
  have p_S : map_SS = ppmap_id S, from 
    @eq_of_is_contr _ (id_sys_ppmap_contr S (@id_type_fam_is_id_sys _ a₀) S) _ _,
  intro a, fapply adjointify, 
  { exact map_RS.1 a },
  { intro r, change map_RR.1 a r = r, rwr p_R },
  { intro p, change map_SS.1 a p = p, rwr p_S }
end                      

@[hott]
def tot_space_contr_id_equiv {A : Type u} {a₀ : A} (R : ppred a₀) : 
  is_contr (Σ (a : A), R.1 a) -> Π a : A, is_equiv (λ p : a₀ = a, p ▸[λ b : A, R.1 b] R.2) :=
assume contr, ppmap_contr_id_equiv R (id_sys_ppmap_contr R (tot_space_contr_id_sys R contr))               

end hott