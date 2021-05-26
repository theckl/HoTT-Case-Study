import hott.algebra.ring set_theory categories.examples categories.cat_limits pathover2

universes u v w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set subset categories hott.trunc
     hott.category_theory.limits hott.sigma

namespace algebra

/- `comm_ring R` is a standard structure on a set `R`:

   Homomorphisms are maps between sets with a `comm_ring` structure preserving addition and 
   multiplication; these laws are propositions, hence being a homomorphism is a proposition. 

   Since it is possible that the same set can be provided with different `comm_ring` structures,
   these cannot be instances. 
   
   Since the set structure underlying `comm_ring` is not bundled we need a variation of `comm_ring`. -/
@[hott]
def comm_ring_set (X : Set.{u}) := comm_ring.{u} X

@[hott]
instance {X : Set.{u}} : has_coe (comm_ring_set X) (comm_ring X) :=
  ⟨λ α : comm_ring_set X, α ⟩

@[hott]
structure is_ring_hom {R S : Set.{u}} (α : comm_ring R) (β : comm_ring S) (f : R -> S) := 
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
def ring_hom_prop {R S : Set} (α : comm_ring_set R) (β : comm_ring_set S) (f : R ⟶ S) : Prop :=
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

@[hott]
def id_ring_hom_set {R : Set} (α : comm_ring_set R) : ring_hom_prop α α (𝟙 R) := 
  id_ring_hom ↑α   

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

@[hott]
def comp_ring_hom_set {R S T : Set} {α : comm_ring_set R} {β : comm_ring_set S} {γ : comm_ring T} {f : R ⟶ S}
  {g : S ⟶ T} (H₁ : ring_hom_prop α β f) (H₂ : ring_hom_prop β γ g) : ring_hom_prop α γ (f ≫ g) :=
@comp_ring_hom _ _ _ α β γ _ _ H₁ H₂   

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
let q := pathover_of_tr_eq (is_prop.elim (p ▸ β₁) β₂) in
(comm_ring_mk_eta γ₁) ⬝ (apd011 comm_ring_mk p q) ⬝ (comm_ring_mk_eta γ₂)⁻¹

@[hott]
def comm_ring_ops_refl_to_refl {X : Set.{u}} (γ : comm_ring X) : 
  comm_ring_ops_eq_to_eq γ γ (refl (comm_ring_to_ops γ)) = refl γ :=
let α := comm_ring_to_ops γ, β := comm_ring_to_laws γ, 
    p := idpath α, q := pathover_of_tr_eq (is_prop.elim (p ▸ β) β), q' := idpatho β in     
have r : q = q', from 
  calc q = pathover_of_tr_eq (is_prop.elim (p ▸ β) β) : rfl
       ... = pathover_of_tr_eq (refl β) : by hsimp
       ... = q' : rfl,    
calc comm_ring_ops_eq_to_eq γ γ (refl α) =
          (comm_ring_mk_eta γ) ⬝ (apd011 comm_ring_mk p q) ⬝ (comm_ring_mk_eta γ)⁻¹ : rfl
     ... = (comm_ring_mk_eta γ) ⬝ (apd011 comm_ring_mk p q') ⬝ (comm_ring_mk_eta γ)⁻¹ : 
           by rwr r
     ... = (comm_ring_mk_eta γ) ⬝ idp ⬝ (comm_ring_mk_eta γ)⁻¹ : rfl
     ... = (comm_ring_mk_eta γ) ⬝ (comm_ring_mk_eta γ)⁻¹ : con_idp _
     ... = idp : con.right_inv _     

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
  comm_ring_hom.map_neg (id_ring_hom γ) = λ a : X, idpath (-a) :=
have H : ∀ a : X, comm_ring_hom.map_neg (id_ring_hom γ) a = idpath (-a), from 
  assume a, is_set.elim _ _,  
eq_of_homotopy H

@[hott]
def ring_hom_is_std_str  {R : Set.{u}} (α β : comm_ring_set.{u} R) : 
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
          exact eq_of_homotopy2_id α₁.add 
        end,
      have p₂ : (id_ring_hom α).map_zero = refl α₁.zero, from rfl,
      have p₃ : eq_of_homotopy (comm_ring_hom.map_neg (id_ring_hom α)) = idpath α₁.neg, from 
        begin rwr comm_ring_hom.id_neg_refl, exact eq_of_homotopy_idp α₁.neg end,
      have p₄ : eq_of_homotopy2 (id_ring_hom α).map_mul = refl α₁.mul, from 
        begin 
          change eq_of_homotopy2 (λ r s : R, refl (α₁.mul r s)) = refl α₁.mul, 
          exact eq_of_homotopy2_id α₁.mul 
        end,
      have p₅ : (id_ring_hom α).map_one = refl α₁.one, from rfl,
      rwr p₁, rwr p₂, rwr p₃, rwr p₄, rwr p₅, hsimp,
      rwr comm_ring_ops_refl_to_refl α },
    /- l_inv : `∀ H : ↥(ring_hom_prop α β (𝟙 R)) × ↥(ring_hom_prop β α (𝟙 R)), G (F H) = H` -/
    { intro H, exact is_prop.elim _ _ } }
end    

/- The category of commutative rings, as the category of `comm_ring` structures on sets -/
@[hott]
def comm_ring_str : std_structure_on Set.{u} :=
  std_structure_on.mk comm_ring_set @ring_hom_prop @id_ring_hom_set @comp_ring_hom_set 
                      @ring_hom_is_std_str                                          

@[hott, reducible] 
def CommRing := std_structure comm_ring_str

@[hott]
def CommRing.mk (carrier : Set.{u}) (comm_ring_str : comm_ring carrier) : CommRing :=
  std_structure.mk carrier comm_ring_str

@[hott]
instance CommRing_to_Set : has_coe CommRing.{u} Set.{u} :=
  ⟨λ R : CommRing, R.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing.{u} :=
  has_coe_to_sort.mk (Type u) (λ R : CommRing, ↥R.carrier)  

@[hott]
instance (R : CommRing) : comm_ring ↥R.carrier := R.str  

/- A criterion to decide whether a subset of a commutative ring given by a predicate is a
   commutative (sub)ring : The ring operation are closed under the predicate. -/ 
@[hott]
class ring_pred_closed {R : CommRing} (P : Setpred R.carrier) :=
  (add : ∀ r s : R, P r -> P s -> P (r + s)) 
  (zero : P 0) 
  (neg : ∀ r : R, P r -> P (-r))
  (mul : ∀ r s : R, P r -> P s -> P (r * s)) 
  (one : P 1)

@[hott]   
def comm_subring {R : CommRing} (P : Setpred R.carrier) [ring_pred_closed P] : 
  comm_ring ↥{r ∈ R.carrier | P r} :=
begin  
  fapply comm_ring_mk,
  { fapply comm_ring_ops.mk, 
    { intros r s, exact ⟨r.1 + s.1, ring_pred_closed.add r.1 s.1 r.2 s.2⟩ }, --add
    { exact ⟨0, ring_pred_closed.zero P⟩ }, --zero
    { intro r, exact ⟨-r.1, ring_pred_closed.neg r.1 r.2⟩ }, --neg
    { intros r s, exact ⟨r.1 * s.1, ring_pred_closed.mul r.1 s.1 r.2 s.2⟩ }, --mul
    { exact ⟨1, ring_pred_closed.one P⟩ } }, --one
  { fapply comm_ring_laws.mk, 
    { intros r s t, hsimp, apply sigma_prop_pr1_inj, hsimp, 
      exact comm_ring.add_assoc r.1 s.1 t.1 }, --add_assoc 
    { intro r, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.zero_add r.1 }, --zero_add
    { intro r, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.add_zero r.1 }, --add_zero 
    { intro r, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.add_left_inv r.1 }, --add_left_inv 
    { intros r s, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.add_comm r.1 s.1 },  --add_comm 
    { intros r s t, hsimp, apply sigma_prop_pr1_inj, hsimp, 
      exact comm_ring.mul_assoc r.1 s.1 t.1 }, --mul_assoc
    { intro r, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.one_mul r.1 }, --one_mul 
    { intro r, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.mul_one r.1 }, --mul_one 
    { intros r s, hsimp, apply sigma_prop_pr1_inj, hsimp, exact comm_ring.mul_comm r.1 s.1 }, --mul_comm
    { intros r s t, hsimp, apply sigma_prop_pr1_inj, hsimp, 
      exact comm_ring.left_distrib r.1 s.1 t.1 }, --left_distrib 
    { intros r s t, hsimp, apply sigma_prop_pr1_inj, hsimp, 
      exact comm_ring.right_distrib r.1 s.1 t.1 }, } --right_distrib
end  

@[hott]
def CommSubring {R : CommRing} (P : Setpred R.carrier) [ring_pred_closed P] : CommRing :=
  CommRing.mk ↥{r ∈ R.carrier | P r} (comm_subring P)

@[hott]
def CommSubring.to_Subset {R : CommRing} (P : Setpred R.carrier) [ring_pred_closed P] : 
  Subset R.carrier :=
{r ∈ R.carrier | P r}    

/- The embedding of the underlying subset of a subring into the underlyimh set of the ring is a 
   ring homomorphism. -/
@[hott]
def comm_subring_embed_hom {R : CommRing} (P : Setpred R.carrier) [ring_pred_closed P]:
  comm_ring_str.H (comm_subring P) R.str (CommSubring.to_Subset P).map :=
begin 
  fapply is_ring_hom.mk, 
  { refl },
  { intros r s, refl },
  { refl },
  { intros r s, refl }
end    

/-  The category `CommRing` has all limits. 

   To prove this we use the criterion in [cat_limits], for which we need to show the following:
   - Products of the underlying sets of commutative rings are also commutative rings.
   - using the subring criterion above we show that the vertices of limit cones of the underlying 
     sets of commutative rings are commutative rings. 
   - The legs and lifts are ring homomorphisms because the subring embedding is a ring 
     homomorphism and the projections from and the lift to product rings are ring homomorphisms. -/
@[hott, reducible]
def CommRing_product_str {J : Set.{v}} (F : J -> CommRing.{v}) : 
  comm_ring (Sections (λ j : J, (F j).carrier)) :=
begin  
  fapply comm_ring_mk,
  { fapply comm_ring_ops.mk, 
    { intros r s, exact λ j, (r j) + (s j) }, --add 
    { exact λ j, 0 }, --zero 
    { intro r, exact λ j, -(r j) }, --neg 
    { intros r s, exact λ j, (r j) * (s j) }, --mul
    { exact λ j,  1 } }, --one
  { fapply comm_ring_laws.mk, 
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_assoc _ _ _ },
                                                                                         --add_assoc
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.zero_add _ }, --zero_add 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_zero _ }, --add_zero 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_left_inv _ }, 
                                                                                     --add_left_inv
    { intros r s, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.add_comm _ _ }, 
                                                                                     --add_comm 
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_assoc _ _ _ },
                                                                                       --mul_assoc 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.one_mul _ }, --one_mul 
    { intro r, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_one _ }, --mul_one 
    { intros r s, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.mul_comm _ _ }, 
                                                                                         --mul_comm
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.left_distrib _ _ _ }, 
                                                                                      --left_distrib
    { intros r s t, hsimp, apply eq_of_homotopy, intro j, hsimp, exact comm_ring.right_distrib _ _ _ } } 
                                                                                    --right_distrib
end    

@[hott]
def CommRing_product {J : Set.{v}} (F : J -> CommRing.{v}) : CommRing :=
  CommRing.mk (Sections (λ j : J, (F j).carrier)) (CommRing_product_str F)

@[hott]
def CommRing_product_proj_hom {J : Set.{v}} (F : J -> CommRing.{v}) : 
  ∀ j : J, comm_ring_str.H (CommRing_product_str F) (F j).str (λ u, u j) :=
begin  
  intro j, fapply is_ring_hom.mk, 
  { refl }, 
  { intros r s, refl }, 
  { refl }, 
  { intros r s, refl },  
end

@[hott]
def ring_limit_pred {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  Setpred (CommRing_product F.obj).carrier :=
set_limit_pred (forget F)  

@[hott, instance]
def ring_pred_is_closed {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) :
  ring_pred_closed (ring_limit_pred F) :=
begin
  fapply ring_pred_closed.mk, 
  { intros r s Hr Hs j k f, change (F.map f).1 (r j + s j) = (r k + s k : F.obj k),
    rwr (F.map f).2.map_add (r j) (s j), 
    have pr : (F.map f).1 (r j) = r k, from Hr f, 
    have ps : (F.map f).1 (s j) = s k, from Hs f,
    rwr pr, rwr ps }, --closed_add
  { intros j k f, change (F.map f).1 0 = (0 : F.obj k), rwr (F.map f).2.map_zero }, 
      --closed_zero
  { intros r Hr j k f, change (F.map f).1 (-(r j)) = (-(r k) : F.obj k),
    rwr comm_ring_hom.map_neg (F.map f).2 (r j), 
    have pr : (F.map f).1 (r j) = r k, from Hr f, rwr pr }, --closed_neg
  { intros r s Hr Hs j k f, change (F.map f).1 (r j * s j) = (r k * s k : F.obj k),
    rwr (F.map f).2.map_mul (r j) (s j), 
    have pr : (F.map f).1 (r j) = r k, from Hr f, 
    have ps : (F.map f).1 (s j) = s k, from Hs f,
    rwr pr, rwr ps }, --closed_mul
  { intros j k f, change (F.map f).1 1 = (1 : F.obj k), rwr (F.map f).2.map_one }, 
      --closed_one
    end  

@[hott]
def limit_comm_ring {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) :
  comm_ring_str.P (set_limit_cone (forget F)).cone.X :=
begin    
  exact @comm_subring (CommRing_product F.obj) (ring_limit_pred F) (ring_pred_is_closed F)
end    

@[hott]
def CommRing_limit_cone {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  limit_cone F :=
begin 
  fapply str_limit_cone (set_limit_cone (forget F)), 
  fapply limit_cone_str_data.mk,
  { exact limit_comm_ring F }, --lc_str
  { intro j, 
    change ↥(comm_ring_str.H (limit_comm_ring F) (F.obj j).str 
             ((CommSubring.to_Subset (ring_limit_pred F)).map ≫ (λ u, u j))), 
    fapply comm_ring_str.comp_H _ (CommRing_product F.obj).str, 
    { exact comm_subring_embed_hom (ring_limit_pred F) },
    { exact CommRing_product_proj_hom F.obj j } }, --lc_legs_H
  { intro s, fapply is_ring_hom.mk, 
    { fapply sigma_eq,
      { change (λ j, (s.π.app j).1 (1 : s.X.carrier)) = (λ j, (1 : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_one }, 
      { apply pathover_of_tr_eq, apply is_prop.elim } },
    { intros t₁ t₂, fapply sigma_eq, 
      { change (λ j, (s.π.app j).1 (t₁ * t₂)) = 
                              (λ j, (((s.π.app j).1 t₁) * ((s.π.app j).1 t₂) : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_mul t₁ t₂ },
      { apply pathover_of_tr_eq, apply is_prop.elim } },  
    { fapply sigma_eq,
      { change (λ j, (s.π.app j).1 (0 : s.X.carrier)) = (λ j, (0 : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_zero }, 
      { apply pathover_of_tr_eq, apply is_prop.elim } },    
    { intros t₁ t₂, fapply sigma_eq, 
      { change (λ j, (s.π.app j).1 (t₁ + t₂)) = 
                              (λ j, (((s.π.app j).1 t₁) + ((s.π.app j).1 t₂) : F.obj j)),
        apply eq_of_homotopy, intro j, hsimp, exact (s.π.app j).2.map_add t₁ t₂ },
      { apply pathover_of_tr_eq, apply is_prop.elim } } } --lift_H
end   

@[hott]
def CommRing_has_limit {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  has_limit F :=
has_limit.mk (CommRing_limit_cone F)

@[hott, instance]
def CommRing_has_limits_of_shape {J : Set.{v}} [precategory.{v} J] :
  has_limits_of_shape J CommRing.{v} :=
has_limits_of_shape.mk (λ F, CommRing_has_limit F)   

/- We now show that the category of commutative rings has all colimits. 
   
   To construct colimits of diagrams of rings we follow the strategy in 
   [mathlib.algebra.category.CommRing.colimits] and define as a quotient of the expressions
   freely generated by the ring operations applied on the elements of the rings in the 
   diagram, modulo the ring relations and the compatibility relations induced by the diagram.

   At this moment, we do not split this up into the construction of the free commutative 
   ring associated to a set, as the left adjoint functor to the forgetful functor, and then
   the quotient by the compatibility relations - it adds an additional layer to calculations
   and proofs, without shortening the construction. -/
@[hott]
inductive expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : Type v
-- one free variable $x_{j,r}$ for each element r in each ring of the diagram
| x_ : Π (j : J) (r : F.obj j), expr
-- Then one generator for each operation
| zero : expr
| one : expr
| neg : expr → expr
| add : expr → expr → expr
| mul : expr → expr → expr

/- The inductive type `expr` is a set. We show this by the encode-decode method, which
  requires a lot of case distinction. There should be potential for automatisation; the
  `injection` tactic may provide short-cuts. -/
@[hott, reducible]
def code_expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  expr F -> expr F -> Type v 
| (expr.x_ j r) (expr.x_ k s) := Σ (p : j = k), (r =[p; λ i : J, F.obj i] s)
| (expr.zero _) (expr.zero _) := One
| (expr.one _) (expr.one _) := One
| (expr.neg x) (expr.neg y) := code_expr x y
| (expr.add x₁ x₂) (expr.add y₁ y₂) := prod (code_expr x₁ y₁) (code_expr x₂ y₂)
| (expr.mul x₁ x₂) (expr.mul y₁ y₂) := prod (code_expr x₁ y₁) (code_expr x₂ y₂)
| _ _ := Zero 

@[hott, reducible]
def code_fun {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  Π (x : expr F), code_expr F x x :=
begin 
  fapply expr.rec, 
  { intros j r, exact ⟨idp, idpo⟩ },
  { exact One.star },
  { exact One.star },
  { intros x cx, exact cx },
  { intros x y cx cy, exact ⟨cx, cy⟩ },
  { intros x y cx cy, exact ⟨cx, cy⟩ }
end  

@[hott, reducible]
def encode_expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) :
  Π (x y : expr F), (x = y) -> code_expr F x y :=
assume x y p, p ▸ (code_fun F x)

@[hott, reducible]
def decode_expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) :
  Π (x y : expr F), (code_expr F x y) -> x = y :=
begin
  intro x, hinduction x; intro y; hinduction y; intro c,
  any_goals { exact Zero.rec _ c}, 
  { exact apd011 expr.x_ c.1 c.2 },
  { exact idp },
  { exact idp },
  { exact ap expr.neg (ih a_1 c) },
  { exact ap011 expr.add (ih_a a_2 c.1) (ih_a_1 a_3 c.2) },
  { exact ap011 expr.mul (ih_a a_2 c.1) (ih_a_1 a_3 c.2) }
end    

@[hott]
def expr_eq_equiv_code {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) :
  Π (x y : expr F), (x = y) ≃ (code_expr F x y) := 
have rinv : Π (x y : expr F) (c : code_expr F x y), 
              encode_expr F x y (decode_expr F x y c) = c, from
  begin 
    intro x, hinduction x; intro y; hinduction y; intro c,
    any_goals { exact Zero.rec _ c}, 
    { sorry },
    { sorry },
    { sorry },
    { sorry },
    { sorry },
    { sorry } 
  end,
have linv : Π (x y : expr F) (p : x = y), decode_expr F x y (encode_expr F x y p) = p, from 
  begin 
    sorry,
  end,    
assume x y,  
  equiv.mk (encode_expr F x y) 
      (is_equiv.adjointify (encode_expr F x y) (decode_expr F x y) (rinv x y) (linv x y))         

@[hott, instance]
def is_set_expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  is_set (expr F) :=
begin 
  fapply is_set.mk, intros x y p q,  
  hinduction q, hinduction x, 
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry }
end     

@[hott, reducible]
def set_expr {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : Set.{v} :=
  Set.mk (expr F) (is_set_expr F)

@[hott]
inductive ring_colim_rel {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  expr F → expr F → Type v
-- Make it an equivalence relation:
| refl : Π (x), ring_colim_rel x x
| symm : Π (x y) (h : ring_colim_rel x y), ring_colim_rel y x
| trans : Π (x y z) (h : ring_colim_rel x y) (k : ring_colim_rel y z), ring_colim_rel x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (r : F.obj j), 
        ring_colim_rel (expr.x_ j' ((F.map f).1 r)) (expr.x_ j r)
-- Then one relation per operation, describing the interaction with `expr.x_`
| zero : Π (j), ring_colim_rel (expr.x_ j 0) (expr.zero F)
| one : Π (j), ring_colim_rel (expr.x_ j 1) (expr.one F)
| neg : Π (j) (x : F.obj j), ring_colim_rel (expr.x_ j (-x)) (expr.neg (expr.x_ j x))
| add : Π (j) (x y : F.obj j), ring_colim_rel (expr.x_ j (x + y)) 
                                              (expr.add (expr.x_ j x) (expr.x_ j y))
| mul : Π (j) (x y : F.obj j), ring_colim_rel (expr.x_ j (x * y)) 
                                              (expr.mul (expr.x_ j x) (expr.x_ j y))
-- Then one relation per argument of each operation
| neg_1 : Π (x x') (r : ring_colim_rel x x'), ring_colim_rel (expr.neg x) (expr.neg x')
| add_1 : Π (x x' y) (r : ring_colim_rel x x'), ring_colim_rel (expr.add x y) (expr.add x' y)
| add_2 : Π (x y y') (r : ring_colim_rel y y'), ring_colim_rel (expr.add x y) (expr.add x y')
| mul_1 : Π (x x' y) (r : ring_colim_rel x x'), ring_colim_rel (expr.mul x y) (expr.mul x' y)
| mul_2 : Π (x y y') (r : ring_colim_rel y y'), ring_colim_rel (expr.mul x y) (expr.mul x y')
-- And one relation per axiom
| zero_add      : Π (x), ring_colim_rel (expr.add (expr.zero F) x) x
| add_zero      : Π (x), ring_colim_rel (expr.add x (expr.zero F)) x
| one_mul       : Π (x), ring_colim_rel (expr.mul (expr.one F) x) x
| mul_one       : Π (x), ring_colim_rel (expr.mul x (expr.one F)) x
| add_left_neg  : Π (x), ring_colim_rel (expr.add (expr.neg x) x) (expr.zero F)
| add_comm      : Π (x y), ring_colim_rel (expr.add x y) (expr.add y x)
| mul_comm      : Π (x y), ring_colim_rel (expr.mul x y) (expr.mul y x)
| add_assoc     : Π (x y z), ring_colim_rel (expr.add (expr.add x y) z) 
                                            (expr.add x (expr.add y z))
| mul_assoc     : Π (x y z), ring_colim_rel (expr.mul (expr.mul x y) z) 
                                            (expr.mul x (expr.mul y z))
| left_distrib  : Π (x y z), ring_colim_rel (expr.mul x (expr.add y z)) 
                                            (expr.add (expr.mul x y) (expr.mul x z))
| right_distrib : Π (x y z), ring_colim_rel (expr.mul (expr.add x y) z) 
                                            (expr.add (expr.mul x z) (expr.mul y z))   

@[hott, reducible]
def ring_colim_mere_rel {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  set_expr F → set_expr F → trunctype.{v} -1 :=
λ x y : set_expr F, ∥ring_colim_rel F x y∥  

@[hott]
def ring_colim_set {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : Set.{v} :=
  set_quotient (ring_colim_mere_rel F)

@[hott]
def ring_colim_str {J : Set.{v}} [precategory.{v} J] (F : J ⥤ CommRing.{v}) : 
  comm_ring (ring_colim_set F) :=
begin 
  let R := ring_colim_set F, let rel := ring_colim_rel F, let mrel := ring_colim_mere_rel F,
  fapply comm_ring_mk,
  { fapply comm_ring_ops.mk, 
    { sorry }, --add
    { sorry }, --zero
    { sorry }, --neg
    { sorry }, --mul
    { sorry } }, --one
  { fapply comm_ring_laws.mk, 
    { sorry }, 
    { sorry }, 
    { sorry }, 
    { sorry },
    { sorry },
    { sorry }, 
    { sorry }, 
    { sorry }, 
    { sorry },
    { sorry },
    { sorry } }
end  

end algebra

end hott
