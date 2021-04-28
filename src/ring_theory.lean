import hott.algebra.ring set_theory categories.examples pathover2

universes u v w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set categories 

namespace algebra

/- `comm_ring R` is a standard structure on a set `R`:

   Homomorphisms are maps between sets with a `comm_ring` structure preserving addition and 
   multiplications; these laws are propositions, hence being a homomorphism is a proposition. 

   Since it is possible that the same set can be provided with different `comm_ring` structures,
   these cannot be instances. -/
@[hott]
structure is_ring_hom {R S : Set} (α : comm_ring R) (β : comm_ring S) (f : R -> S) := 
  (map_one : f 1 = 1)
  (map_mul : ∀ a b : R, f (a * b) = f a * f b)
  (map_zero : f 0 = 0)
  (map_add : ∀ a b : R, f (a + b) = f a + f b)

@[hott]
def is_ring_hom_eta {R S : Set} {α : comm_ring R} {β : comm_ring S} {f : R -> S}
  (rh : is_ring_hom α β f) : 
  rh = is_ring_hom.mk rh.map_one rh.map_mul rh.map_zero rh.map_add :=
begin hinduction rh, refl end   

@[hott, instance]
def is_prop_is_ring_hom {R S : Set} (α : comm_ring R) (β : comm_ring S) (f : R ⟶ S) :
  is_prop (is_ring_hom α β f) :=
have H_one : ∀ p q : f 1 = 1, p = q, from assume p q, is_set.elim p q, 
have H_mul : ∀ p q : ∀ a b : R, f (a * b) = f a * f b, p = q, from 
  assume p q, is_prop.elim p q,
have H_zero : ∀ p q : f 0 = 0, p = q, from assume p q, is_set.elim p q,
have H_add : ∀ p q : ∀ a b : R, f (a + b) = f a + f b, p = q, from 
  assume p q, is_prop.elim p q, 
have H : ∀ rh₁ rh₂ : is_ring_hom α β f, rh₁ = rh₂, from
  assume rh₁ rh₂, 
  calc rh₁ = is_ring_hom.mk rh₁.map_one rh₁.map_mul rh₁.map_zero rh₁.map_add : is_ring_hom_eta rh₁
       ... = is_ring_hom.mk rh₂.map_one rh₂.map_mul rh₂.map_zero rh₂.map_add : 
             ap_4 is_ring_hom.mk (H_one rh₁.map_one rh₂.map_one) (H_mul rh₁.map_mul rh₂.map_mul) 
                                 (H_zero rh₁.map_zero rh₂.map_zero) (H_add rh₁.map_add rh₂.map_add)
       ... = rh₂ : (is_ring_hom_eta rh₂)⁻¹,
is_prop.mk H 

@[hott]
def ring_hom_prop {R S : Set} (α : comm_ring R) (β : comm_ring S) (f : R ⟶ S) : Prop :=
  trunctype.mk (is_ring_hom α β f) (is_prop_is_ring_hom α β f)

/- The identity map on a set is a ring homomorphism with respect to any ring structure. -/
@[hott]
def id_ring_hom {R : Set} (α : comm_ring R) : ring_hom_prop α α (𝟙 R) :=
  let id_R := id_map R in
  have one_R : id_R 1 = 1, by refl,
  have mul_R : ∀ r s : R, id_R (r * s) = (id_R r) * (id_R s), 
    by intros r s; refl,
  have zero_R : id_R 0 = 0, by refl,
  have add_R : ∀ r s : R, id_R (r + s) = (id_R r) + (id_R s), 
    by intros r s; refl,
  is_ring_hom.mk one_R mul_R zero_R add_R 

/- The composition of two maps that are ring homomorphisms is a ring homomorphism. -/
def comp_ring_hom {R S T : Set} {α : comm_ring R} {β : comm_ring S} {γ : comm_ring T} {f : R ⟶ S}
  {g : S ⟶ T} (H₁ : ring_hom_prop α β f) (H₂ : ring_hom_prop β γ g) : ring_hom_prop α γ (f ≫ g) :=
let h := λ r : R, g (f r) in   
have h_one : h 1 = 1, from
    calc h 1 = g (f 1) : rfl
         ... = g 1 : by rwr H₁.map_one
         ... = 1 : by rwr H₂.map_one,
  have h_mul : ∀ r₁ r₂ : R, h (r₁ * r₂) = h r₁ * h r₂, from assume r₁ r₂, 
    calc h (r₁ * r₂) = g (f (r₁ * r₂)) : rfl
         ... = g (f r₁ * f r₂) : by rwr H₁.map_mul
         ... = g (f r₁) * g (f r₂) : by rwr H₂.map_mul
         ... = h r₁ * h r₂ : rfl,
  have h_zero : h 0 = 0, from 
    calc h 0 = g (f 0) : rfl
         ... = g 0 : by rwr H₁.map_zero
         ... = 0 : by rwr H₂.map_zero,
  have h_add : ∀ r₁ r₂ : R, h (r₁ + r₂) = h r₁ + h r₂, from assume r₁ r₂, 
    calc h (r₁ + r₂) = g (f (r₁ + r₂)) : rfl
         ... = g (f r₁ + f r₂) : by rwr H₁.map_add
         ... = g (f r₁) + g (f r₂) : by rwr H₂.map_add
         ... = h r₁ + h r₂ : rfl,
is_ring_hom.mk h_one h_mul h_zero h_add 

/- We now start the proof that `is_ring_hom` is a standard structure on sets. 

   We first refactor the definition of a `comm_ring` structure, to simplify proofs
   of equality, by splitting it up into two structures of operations and laws they
   need to satisfy. 
   
   I don't see how the instance mechanism can be used here to write `add` as `+`
   etc. The problem is that different additions will appear for the same set `X`;
   a symbol like `+ₐ` would be better, but cannot be obtained from `has_add X`. -/
@[hott]
structure comm_ring_ops (X : Set.{u}) :=
  (add : X -> X -> X)
  (zero : X)
  (neg : X -> X)
  (mul : X -> X -> X)
  (one : X)

@[hott, hsimp, reducible]
def comm_ring_to_ops {X : Set.{u}} (γ : comm_ring X) : comm_ring_ops X :=
  comm_ring_ops.mk γ.add γ.zero γ.neg γ.mul γ.one

@[hott]
structure comm_ring_laws {X : Set.{u}} (α : comm_ring_ops X) :=
  (add_assoc : Π (a b c : X), α.add (α.add a b) c = α.add a (α.add b c)) 
  (zero_add : Π a : X, α.add α.zero a = a)
  (add_zero : Π a : X, α.add a α.zero = a)
  (neg_add : Π a : X, α.add (α.neg a) a = α.zero)
  (add_comm : Π a b : X, α.add a b = α.add b a) 
  (mul_assoc : Π (a b c : X), α.mul (α.mul a b) c = α.mul a (α.mul b c)) 
  (one_mul : Π a : X, α.mul α.one a = a)
  (mul_one : Π a : X, α.mul a α.one = a)
  (mul_comm : Π a b : X, α.mul a b = α.mul b a)
  (right_distrib : Π a b c : X, α.mul a (α.add b c) = 
                                  α.add (α.mul a b) (α.mul a c)) 
  (left_distrib : Π a b c : X, α.mul (α.add a b) c = 
                                  α.add (α.mul a c) (α.mul b c))

@[hott, instance]
def prop_comm_ring_laws {X : Set.{u}} (α : comm_ring_ops X) : 
  is_prop (comm_ring_laws α) :=
have H : ∀ β₁ β₂ : comm_ring_laws α, β₁ = β₂, from 
  begin 
    intros β₁ β₂, hinduction β₁, hinduction β₂, 
    apply ap_11 (@comm_ring_laws.mk X α); 
    { { apply eq_of_homotopy3, intros a b c, exact @is_set.elim X _ _ _ _ _ } <|> 
      { apply eq_of_homotopy2, intros a b, exact @is_set.elim X _ _ _ _ _ } <|>
      { apply eq_of_homotopy, intros a, exact @is_set.elim X _ _ _ _ _ } },  
  end, 
is_prop.mk H  

@[hott, hsimp]
def comm_ring_to_laws {X : Set.{u}} (γ : comm_ring X) : 
  comm_ring_laws (comm_ring_to_ops γ) :=
let α := comm_ring_to_ops γ in
have add_eq : α.add = γ.add, from rfl, 
have zero_eq : α.zero = γ.zero, from rfl,
have neg_eq : α.neg = γ.neg, from rfl,
have mul_eq : α.mul = γ.mul, from rfl,
have one_eq : α.one = γ.one, from rfl, 
begin 
  constructor, 
  { rwr add_eq, exact γ.add_assoc },
  { rwr zero_eq, rwr add_eq, exact γ.zero_add },
  { rwr zero_eq, rwr add_eq, exact γ.add_zero },
  { rwr zero_eq, rwr add_eq, rwr neg_eq, exact γ.add_left_inv },
  { rwr add_eq, exact γ.add_comm },
  { rwr mul_eq, exact γ.mul_assoc },
  { rwr mul_eq, rwr one_eq, exact γ.one_mul },
  { rwr mul_eq, rwr one_eq, exact γ.mul_one },
  { rwr mul_eq, exact γ.mul_comm },
  { rwr mul_eq, rwr add_eq, exact γ.left_distrib },
  { rwr mul_eq, rwr add_eq, exact γ.right_distrib }
end

@[hott, hsimp]
def comm_ring_mk {X : Set.{u}} (α : comm_ring_ops X) (β : comm_ring_laws α) :
  comm_ring X :=
comm_ring.mk X.struct α.add β.add_assoc α.zero β.zero_add β.add_zero α.neg β.neg_add
               β.add_comm α.mul β.mul_assoc α.one β.one_mul β.mul_one 
               β.right_distrib β.left_distrib β.mul_comm

@[hott]
def comm_ring_mk_eta {X : Set.{u}} : Π (γ : comm_ring X), 
  γ = comm_ring_mk (comm_ring_to_ops γ) (comm_ring_to_laws γ) := 
assume γ, 
have is_prop_struct : is_prop (is_set X), from is_prop_is_trunc 0 X,  
have p : X.struct = γ.is_set_carrier, from is_prop.elim _ _,    
begin
  hinduction γ,
  hsimp, rwr p 
end                     

@[hott]
def comm_ring_ops_eq_to_eq {X : Set.{u}} (γ₁ γ₂ : comm_ring X) :
  comm_ring_to_ops γ₁ = comm_ring_to_ops γ₂ -> γ₁ = γ₂ :=
let α₁ := comm_ring_to_ops γ₁, α₂ := comm_ring_to_ops γ₂,
    β₁ := comm_ring_to_laws γ₁, β₂ := comm_ring_to_laws γ₂ in 
assume p,
have q : β₁ =[p] β₂, from 
  begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,     
calc γ₁ = comm_ring_mk α₁ β₁ : comm_ring_mk_eta γ₁
    ... = comm_ring_mk α₂ β₂ : apd011 comm_ring_mk p q
    ... = γ₂ : by rwr <- comm_ring_mk_eta γ₂

@[hott]
def comm_ring_ops_refl_to_refl {X : Set.{u}} (γ : comm_ring X) : 
  comm_ring_ops_eq_to_eq γ γ (refl (comm_ring_to_ops γ)) = refl γ :=
sorry    

@[hott]
def comm_ring_hom.map_neg {X Y : Set.{u}} {γ₁ : comm_ring.{u} X} {γ₂ : comm_ring.{u} Y} 
  {f : X -> Y} (hom_str : is_ring_hom γ₁ γ₂ f) : ∀ a : X, f (-a) = -(f a) :=
assume a,  
calc f (-a) = 0 + f (-a) : (@comm_ring.zero_add _ γ₂ (f (-a)))⁻¹
     ... = (-(f a) + f a) + f (-a) : ap (λ b : Y, @comm_ring.add _ γ₂ b (f (-a))) 
                                        (@comm_ring.add_left_inv _ γ₂ (f a))⁻¹
     ... = -(f a) + (f a + f (-a)) : @comm_ring.add_assoc _ γ₂ _ _ _
     ... = -(f a) + (f (-a) + f a) : ap (λ b : Y, @comm_ring.add _ γ₂ (-(f a)) b) 
                                        (@comm_ring.add_comm _ γ₂ _ _)
     ... = -(f a) + f (-a + a) : by rwr hom_str.map_add 
     ... = -(f a) + f 0 : ap (λ b : X, @comm_ring.add _ γ₂ (-(f a)) (f b))
                           (@comm_ring.add_left_inv _ γ₁ a) 
     ... = -(f a) + 0 : by rwr hom_str.map_zero                                                                                              
     ... = -(f a) : @comm_ring.add_zero _ γ₂ (-(f a))   

@[hott]
def comm_ring_hom.id_neg_refl {X : Set.{u}} {γ : comm_ring X} :
  comm_ring_hom.map_neg (id_ring_hom γ) = ∀ a : X, @idp _ (γ.add a) :=
sorry  

@[hott]
def ring_hom_is_std_str  {R : Set} (α β : comm_ring R) : 
  (ring_hom_prop α β (𝟙 R) × ring_hom_prop β α (𝟙 R)) ≃ α = β :=
begin
  fapply equiv.mk, 
  /- `F : ↥(ring_hom_prop α β (𝟙 R)) × ↥(ring_hom_prop β α (𝟙 R)) → α = β` -/
  { intro H,
    let α₁ := comm_ring_to_ops α, let β₁ := comm_ring_to_ops β,
    fapply comm_ring_ops_eq_to_eq α β,
    change comm_ring_ops.mk α₁.add α₁.zero α₁.neg α₁.mul α₁.one = 
           comm_ring_ops.mk β₁.add β₁.zero β₁.neg β₁.mul β₁.one,
    fapply ap_5,       
    { exact eq_of_homotopy2 H.1.map_add },
    { exact H.1.map_zero },
    { exact eq_of_homotopy (comm_ring_hom.map_neg H.1) },
    { exact eq_of_homotopy2 H.1.map_mul },
    { exact H.1.map_one } },
  { fapply adjointify,
    /- `G : α = β -> ↥(ring_hom_prop α β (𝟙 R)) × ↥(ring_hom_prop β α (𝟙 R))` -/ 
    { intro p, rwr p, exact (id_ring_hom β, id_ring_hom β) },
    /- r_inv : `∀ p : α = β, F (G p) = p` -/
    { intro p, hinduction p, rwr idp_inv, rwr idp_tr, hsimp, 
      let α₁ := comm_ring_to_ops α,
      have p₁ : eq_of_homotopy2 (id_ring_hom α).map_add = refl α₁.add, from 
        begin 
          change eq_of_homotopy2 (λ r s : R, refl (α₁.add r s)) = refl α₁.add, 
          exact eq_of_homotopy2_refl α₁.add 
        end,
      have p₂ : (id_ring_hom α).map_zero = refl α₁.zero, from rfl,
      have p₃ : eq_of_homotopy (comm_ring_hom.map_neg (id_ring_hom α)) = refl α₁.neg, from 
        begin 
          change eq_of_homotopy (λ r : R, refl (α₁.neg r)) = refl α₁.neg, 
          exact eq_of_homotopy_refl α₁.neg 
        end,
      have p₄ : eq_of_homotopy2 (id_ring_hom α).map_mul = refl α₁.mul, from 
        begin 
          change eq_of_homotopy2 (λ r s : R, refl (α₁.mul r s)) = refl α₁.mul, 
          exact eq_of_homotopy2_refl α₁.mul 
        end,
      have p₅ : (id_ring_hom α).map_one = refl α₁.one, from rfl,
      rwr p₁, rwr p₂, rwr p₃, rwr p₄, rwr p₅, hsimp,
      rwr comm_ring_ops_refl_to_refl α },
    /- l_inv : `∀ H : ↥(ring_hom_prop α β (𝟙 R)) × ↥(ring_hom_prop β α (𝟙 R)), G (F H) = H` -/
    { intro H, exact is_prop.elim _ _ } }
end    

/- Bundled structure of commutative rings -/
@[hott] 
structure CommRing :=
(carrier : Set) (struct : comm_ring carrier)

@[hott]
instance CommRing_to_Set : has_coe CommRing.{u} Set.{u} :=
  ⟨CommRing.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing.{u} :=
  has_coe_to_sort.mk (Type u) (λ R : CommRing, ↥R.carrier)  

attribute [instance] CommRing.struct

/- We now construct the category structure on commutative rings. 

   We first define ring homomorphisms without inheritance, as for 
   this project, we do not need homomorphisms of monoids and groups. -/
@[hott]
structure ring_hom (M N : CommRing.{u}) :=
  (to_fun : M -> N)
  (map_one : to_fun 1 = 1)
  (map_mul : ∀ a b : M, to_fun (a * b) = to_fun a * to_fun b)
  (map_zero : to_fun 0 = 0)
  (map_add : ∀ a b : M, to_fun (a + b) = to_fun a + to_fun b)

infixr ` →+* `:25 := ring_hom

@[hott]
instance ring_hom_to_fun (M N : CommRing) : 
  has_coe_to_fun (ring_hom M N) :=
⟨λ _, M -> N, λ h, h.to_fun⟩  

/- Needed for calculations. -/
@[hott]
def rh_map_one {R S : CommRing} (f : R →+* S) :
  f 1 = 1 :=
f.map_one   

@[hott]
def rh_map_mul {R S : CommRing} (f : R →+* S) :
  ∀ r₁ r₂ : R, f (r₁ * r₂) = f r₁ * f r₂ :=
f.map_mul  

@[hott]
def rh_map_zero {R S : CommRing} (f : R →+* S) :
  f 0 = 0 :=
f.map_zero   

@[hott]
def rh_map_add {R S : CommRing} (f : R →+* S) :
  ∀ r₁ r₂ : R, f (r₁ + r₂) = f r₁ + f r₂ :=
f.map_add

/- We show the HoTTism that all the ring homomrphisms between two
   commutative rings are a set by showing that ring homomorphisms are completely
   determined by the map between the underlying sets. This means that the
   forgetful functor from rings to sets is faithful. 
   
   Most of the proofs use that the structure equations are propositions
   because the source and target of the homomorphisms are sets. -/
@[hott]
def ring_hom_eta {M N : CommRing} (f : M →+* N) : 
  f = ring_hom.mk f.to_fun f.map_one f.map_mul f.map_zero f.map_add :=
begin hinduction f, refl end

@[hott, hsimp]
def rh_fun_eq {M N : CommRing} {f g : M →+* N} (p : f = g) : 
  f.to_fun = g.to_fun :=
ap ring_hom.to_fun p 

@[hott, hsimp, reducible]
def rh_fun_one_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_one =[p; λ h : M -> N, h 1 = 1] g.map_one :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end  

@[hott, hsimp]
def rh_fun_mul_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_mul 
    =[p; λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] g.map_mul :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end    

@[hott, hsimp]
def rh_fun_zero_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_zero =[p; λ h : M -> N, h 0 = 0] g.map_zero :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end  

@[hott, hsimp]
def rh_fun_add_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_add 
    =[p; λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] g.map_add :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end

@[hott, hsimp]
def rh_fun_to_hom {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) : f = g :=
  (ring_hom_eta f) ⬝ 
  (apd01111 ring_hom.mk p (rh_fun_one_eq p) (rh_fun_mul_eq p) 
                          (rh_fun_zero_eq p) (rh_fun_add_eq p)) ⬝ 
  (ring_hom_eta g)⁻¹

/- I don't understand why this proof must be so long. I was not able to tell
   Lean how to process the `idp` and `refl` arguments automatically. -/
@[hott]
def rh_fun_hom_rinv {M N : CommRing} {f g : M →+* N} (p : f = g) :
  rh_fun_to_hom (rh_fun_eq p) = p :=
have r₁ : rh_fun_one_eq (refl ⇑f) = idpo, by hsimp; refl, 
have r₂ : rh_fun_mul_eq (refl ⇑f) = idpo, by hsimp; refl,
have r₃ : rh_fun_zero_eq (refl ⇑f) = idpo, by hsimp; refl, 
have r₄ : rh_fun_add_eq (refl ⇑f) = idpo, by hsimp; refl,
have q : apd01111 ring_hom.mk (refl ⇑f) (rh_fun_one_eq (refl ⇑f)) 
         (rh_fun_mul_eq (refl ⇑f)) (rh_fun_zero_eq (refl ⇑f))
         (rh_fun_add_eq (refl ⇑f)) = idp, 
  by rwr r₁; rwr r₂; rwr r₃; rwr r₄; hsimp,   
begin 
  hinduction p, change rh_fun_to_hom (refl f) = refl f,
  change (ring_hom_eta f) ⬝ _ ⬝ (ring_hom_eta f)⁻¹ = idp,
  rwr q, rwr con_idp, rwr con.right_inv 
end

@[hott]
def rh_fun_hom_linv {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  rh_fun_eq (rh_fun_to_hom p) = p :=
@is_set.elim (M -> N) _ _ _ _ _  

@[hott]
def rh_fun_eq_equiv_hom_eq {M N : CommRing} (f g : M →+* N) : 
  (⇑f = g) ≃ (f = g) :=
equiv.mk rh_fun_to_hom (adjointify rh_fun_to_hom rh_fun_eq 
                                   rh_fun_hom_rinv rh_fun_hom_linv)   

@[hott, instance]
def ring_hom_is_set (M N : CommRing) : is_set (M →+* N) :=
  have set_eq_eq : ∀ (g h : M →+* N) (p q : g = h), p = q, from
    assume g h,
    have is_prop_fun_eq : is_prop (⇑g = h), from 
      is_prop.mk (@is_set.elim (M -> N) _ _ _),
    have is_prop_hom_eq : is_prop (g = h), from 
      is_trunc_equiv_closed -1 (rh_fun_eq_equiv_hom_eq g h) is_prop_fun_eq,
    @is_prop.elim _ is_prop_hom_eq, 
  is_set.mk _ set_eq_eq   

/- Next, we define the category structure on `CommRing`. -/
@[hott, instance]
def ring_has_hom : has_hom CommRing :=
  has_hom.mk (λ R S : CommRing, Set.mk (ring_hom R S) (ring_hom_is_set R S))

@[hott, hsimp, reducible]
def id_CommRing (R : CommRing) : R ⟶ R :=
  let id_R := @set.id R in
  have one_R : id_R 1 = 1, by refl,
  have mul_R : ∀ r s : R, id_R (r * s) = (id_R r) * (id_R s), 
    by intros r s; refl,
  have zero_R : id_R 0 = 0, by refl,
  have add_R : ∀ r s : R, id_R (r + s) = (id_R r) + (id_R s), 
    by intros r s; refl,
  ring_hom.mk id_R one_R mul_R zero_R add_R

@[hott, hsimp, reducible]
def comp_CommRing {R S T : CommRing} (f : R →+* S) (g : S →+* T) : R →+* T :=
  let h := λ r : R, g (f r) in
  have h_one : h 1 = 1, from
    calc h 1 = g (f 1) : rfl
         ... = g 1 : by rwr rh_map_one
         ... = 1 : by rwr rh_map_one,
  have h_mul : ∀ r₁ r₂ : R, h (r₁ * r₂) = h r₁ * h r₂, from assume r₁ r₂, 
    calc h (r₁ * r₂) = g (f (r₁ * r₂)) : rfl
         ... = g (f r₁ * f r₂) : by rwr rh_map_mul
         ... = g (f r₁) * g (f r₂) : by rwr rh_map_mul
         ... = h r₁ * h r₂ : rfl,
  have h_zero : h 0 = 0, from 
    calc h 0 = g (f 0) : rfl
         ... = g 0 : by rwr rh_map_zero
         ... = 0 : by rwr rh_map_zero,
  have h_add : ∀ r₁ r₂ : R, h (r₁ + r₂) = h r₁ + h r₂, from assume r₁ r₂, 
    calc h (r₁ + r₂) = g (f (r₁ + r₂)) : rfl
         ... = g (f r₁ + f r₂) : by rwr rh_map_add
         ... = g (f r₁) + g (f r₂) : by rwr rh_map_add
         ... = h r₁ + h r₂ : rfl,
  ring_hom.mk h h_one h_mul h_zero h_add

@[hott, instance]
def CommRing_cat_struct : category_struct CommRing :=
  category_struct.mk id_CommRing @comp_CommRing

/- The equalities of homomorphisms making up a precategory follow from 
   the equalities of the maps on the underlying sets. -/
@[hott, hsimp]
def id_comp_CommRing {R S : CommRing.{u}} : Π (f : R ⟶ S), 
  𝟙 R ≫ f = f :=
assume f,  
have hom_eq : ∀ r : R, (𝟙 R ≫ f) r = f r, from assume r, rfl,
have fun_eq : ⇑(𝟙 R ≫ f) = f, from eq_of_homotopy hom_eq,   
rh_fun_to_hom fun_eq  

@[hott, hsimp]
def comp_id_CommRing {R S : CommRing.{u}} : Π (f : R ⟶ S), 
  f ≫ 𝟙 S = f :=
assume f,  
have hom_eq : ∀ r : R, (f ≫ 𝟙 S) r = f r, from assume r, rfl,
have fun_eq : ⇑(f ≫ 𝟙 S) = f, from eq_of_homotopy hom_eq,   
rh_fun_to_hom fun_eq

@[hott, hsimp]
def assoc_CommRing {R S T U : CommRing.{u}} : 
  Π (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
assume f g h,
have hom_eq : ∀ r : R, ((f ≫ g) ≫ h) r = (f ≫ (g ≫ h)) r, from assume r, rfl,
have fun_eq : ⇑((f ≫ g) ≫ h) = f ≫ (g ≫ h), from eq_of_homotopy hom_eq, 
rh_fun_to_hom fun_eq 

@[hott, instance]
def CommRing_precategory : precategory CommRing.{u} :=
  precategory.mk @id_comp_CommRing @comp_id_CommRing @assoc_CommRing

/- We now show that `CommRing` is a category. 

   First we use univalence to construct an equality of the underlying sets
   from an isomorphy of rings. This is noncomputable. -/
@[hott, reducible]
def CommRing_isotoTypeid (R S : CommRing) : R ≅ S -> ↥R = ↥S :=
  assume isoRS,
  let h := ⇑isoRS.hom, i := ⇑isoRS.inv in
  have r_inv : ∀ s : S, h (i s) = s, from assume s, 
    calc h (i s) = (isoRS.inv ≫ isoRS.hom) s : by refl 
         ... = (id_CommRing S) s : by rwr isoRS.r_inv
         ... = s : by refl,
  have l_inv : ∀ r : R, i (h r) = r, from assume r, 
    calc i (h r) = (isoRS.hom ≫ isoRS.inv) r : by refl 
         ... = (id_CommRing R) r : by rwr isoRS.l_inv
         ... = r : by refl, 
  have equivRS : R ≃ S, from equiv.mk h (adjointify h i r_inv l_inv),             
  ua equivRS

@[hott]
def CommRing_isotoSetid (R S : CommRing) : R ≅ S -> R.carrier = S.carrier :=
  assume isoRS,
  set_eq_equiv_car_eq.symm.to_fun (CommRing_isotoTypeid R S isoRS)

@[hott]
def cast_iso_eq {R S : CommRing} (iso : R ≅ S) :
  ∀ r : R, cast (CommRing_isotoTypeid R S iso) r = iso.hom r :=
by intro r; rwr cast_ua   

end algebra

end hott
