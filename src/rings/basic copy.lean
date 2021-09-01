import hott.algebra.ring sets.basic categories.examples categories.cat_limits init2 types2
       hott.types.prod hott.algebra.relation categories.cat_colimits

universes u u' v w
hott_theory

namespace hott
open hott.is_trunc hott.is_equiv hott.algebra hott.set subset categories hott.trunc
     hott.category_theory.limits hott.sigma hott.prod hott.relation 
     hott.category_theory.colimits hott.ulift

namespace algebra

/- We construct the category of rings as a first-order signature category of operations and 
   laws governing them. 
   
   We first need to define the first-order signature. -/
@[hott]
inductive ring_ops : Type 0 
| add : ring_ops
| zero : ring_ops 
| neg : ring_ops 
| mul : ring_ops 
| one : ring_ops

@[hott]
def ring_ops_is_set : is_set ring_ops := 
  have ring_ops_equiv : ring_ops ≃ fin_Set 5, from 
  begin 
    fapply equiv.MK,
    { sorry },
    { sorry },
    { sorry },
    { sorry }
  end,
  is_trunc_equiv_closed_rev 0 ring_ops_equiv (fin_Set 5).struct 

@[hott]
def ring_ops_Set : Set.{0} := Set.mk ring_ops ring_ops_is_set

@[hott]
def ring_signature : fo_signature :=
  sorry   

/- `comm_ring R` is a standard structure on a set `R`:

   Homomorphisms are maps between sets with a `comm_ring` structure preserving addition and 
   multiplication; these laws are propositions, hence being a homomorphism is a proposition. 

   Since it is possible that the same set can be provided with different `comm_ring` structures,
   these cannot be instances. 
   
   Since the set structure underlying `comm_ring` is not bundled we need a variation of `comm_ring`. -/
@[hott]
def comm_ring_set (X : Set) := comm_ring X

@[hott]
instance {X : Set} : has_coe (comm_ring_set X) (comm_ring X) :=
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
structure comm_ring_ops (X : Set) :=
  (add : X -> X -> X)
  (zero : X)
  (neg : X -> X)
  (mul : X -> X -> X)
  (one : X)

@[hott, hsimp, reducible]
def comm_ring_to_ops {X : Set} (γ : comm_ring X) : comm_ring_ops X :=
  comm_ring_ops.mk γ.add γ.zero γ.neg γ.mul γ.one

@[hott]
structure comm_ring_laws {X : Set} (α : comm_ring_ops X) :=
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
def comm_ring_to_laws {X : Set} (γ : comm_ring X) : 
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
def comm_ring_mk {X : Set} (α : comm_ring_ops X) (β : comm_ring_laws α) :
  comm_ring X :=
comm_ring.mk X.struct α.add β.add_assoc α.zero β.zero_add β.add_zero α.neg β.neg_add
               β.add_comm α.mul β.mul_assoc α.one β.one_mul β.mul_one 
               β.right_distrib β.left_distrib β.mul_comm

@[hott]
def comm_ring_mk_eta {X : Set} : Π (γ : comm_ring X), 
  γ = comm_ring_mk (comm_ring_to_ops γ) (comm_ring_to_laws γ) := 
assume γ, 
have is_prop_struct : is_prop (is_set X), from is_prop_is_trunc 0 X,  
have p : X.struct = γ.is_set_carrier, from is_prop.elim _ _,    
begin
  hinduction γ,
  hsimp, rwr p 
end                     

@[hott]
def comm_ring_ops_eq_to_eq {X : Set} (γ₁ γ₂ : comm_ring X) :
  comm_ring_to_ops γ₁ = comm_ring_to_ops γ₂ -> γ₁ = γ₂ :=
let α₁ := comm_ring_to_ops γ₁, α₂ := comm_ring_to_ops γ₂,
    β₁ := comm_ring_to_laws γ₁, β₂ := comm_ring_to_laws γ₂ in 
assume p,
let q := pathover_of_tr_eq (is_prop.elim (p ▸ β₁) β₂) in
(comm_ring_mk_eta γ₁) ⬝ (apd011 comm_ring_mk p q) ⬝ (comm_ring_mk_eta γ₂)⁻¹

@[hott]
def comm_ring_ops_refl_to_refl {X : Set} (γ : comm_ring X) : 
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
def comm_ring_hom.map_neg {X Y : Set} {γ₁ : comm_ring X} {γ₂ : comm_ring Y} 
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
def comm_ring_hom.id_neg_refl {X : Set} {γ : comm_ring X} :
  comm_ring_hom.map_neg (id_ring_hom γ) = λ a : X, idpath (-a) :=
have H : ∀ a : X, comm_ring_hom.map_neg (id_ring_hom γ) a = idpath (-a), from 
  assume a, is_set.elim _ _,  
eq_of_homotopy.{u u} H

@[hott]
def ring_hom_is_std_str {R : Set.{u}} (α β : comm_ring_set R) : 
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

/- The category of commutative rings, as the category of `comm_ring`-structures on sets -/
@[hott]
def comm_ring_str : std_structure_on Set :=
  std_structure_on.mk comm_ring_set @ring_hom_prop @id_ring_hom_set @comp_ring_hom_set 
                      @ring_hom_is_std_str                                          

@[hott, reducible] 
def CommRing := std_structure comm_ring_str

@[hott]
def CommRing.mk (carrier : Set) (comm_ring_str : comm_ring carrier) : CommRing :=
  std_structure.mk carrier comm_ring_str

@[hott]
instance CommRing_to_Set : has_coe CommRing Set :=
  ⟨λ R : CommRing, R.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing :=
  has_coe_to_sort.mk (Type u) (λ R : CommRing, R.carrier)  

@[hott]
instance (R : CommRing) : comm_ring ↥R.carrier := R.str  

/- A criterion to decide whether a subset of a commutative ring given by a predicate is a
   commutative (sub)ring : The ring operation are closed under the predicate. -/ 
@[hott]
class ring_pred_closed {R : CommRing} (P : Subset R.carrier) :=
  (add : ∀ r s : R, P r -> P s -> P (r + s)) 
  (zero : P 0) 
  (neg : ∀ r : R, P r -> P (-r))
  (mul : ∀ r s : R, P r -> P s -> P (r * s)) 
  (one : P 1)

@[hott]   
def comm_subring {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P] : 
  comm_ring ↥P :=
begin  
  fapply @comm_ring_mk (pred_Set P),
  { fapply comm_ring_ops.mk, 
    { intros r s, exact ⟨r.1 + s.1, ring_pred_closed.add r.1 s.1 r.2 s.2⟩ }, --add
    { exact ⟨0, ring_pred_closed.zero P⟩ }, --zero
    { intro r, exact ⟨-r.1, ring_pred_closed.neg r.1 r.2⟩ }, --neg
    { intros r s, exact ⟨r.1 * s.1, ring_pred_closed.mul r.1 s.1 r.2 s.2⟩ }, --mul
    { exact ⟨1, ring_pred_closed.one P⟩ } }, --one
  { fapply comm_ring_laws.mk, 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.add_assoc r.1 s.1 t.1 }, --add_assoc 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.zero_add r.1 }, --zero_add
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_zero r.1 }, --add_zero 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_left_inv r.1 }, --add_left_inv 
    { intros r s, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.add_comm r.1 s.1 },  --add_comm 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.mul_assoc r.1 s.1 t.1 }, --mul_assoc
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.one_mul r.1 }, --one_mul 
    { intro r, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.mul_one r.1 }, --mul_one 
    { intros r s, hsimp, apply sigma_Prop_eq, hsimp, exact comm_ring.mul_comm r.1 s.1 }, --mul_comm
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.left_distrib r.1 s.1 t.1 }, --left_distrib 
    { intros r s t, hsimp, apply sigma_Prop_eq, hsimp, 
      exact comm_ring.right_distrib r.1 s.1 t.1 }, } --right_distrib
end  

@[hott]
def CommSubring {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P] : CommRing :=
  CommRing.mk (pred_Set P) (comm_subring P)

@[hott]
def CommSubring.to_Subset {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P] : 
  Subset R.carrier :=
{r ∈ R.carrier | P r}    

/- The embedding of the underlying subset of a subring into the underlying set of the ring is a 
   ring homomorphism. -/
@[hott]
def comm_subring_embed_hom {R : CommRing} (P : Subset R.carrier) [ring_pred_closed P]:
  comm_ring_str.H (CommSubring P).str R.str (pred_Set_map (CommSubring.to_Subset P)) :=
begin 
  fapply is_ring_hom.mk, 
  { refl },
  { intros r s, refl },
  { refl },
  { intros r s, refl }
end     

/- Units of a ring as a bundled structure. Since for a given ring element there is at most a 
   unique inverse we can also define a predicate identifying invertible ring elements. -/
@[hott]
structure units (R : CommRing) :=
(val : R)
(inv : R)
(val_inv : val * inv = 1)

namespace units

@[hott] 
instance (R : CommRing) : has_coe (units R) R := ⟨val⟩

end units

open units

@[hott]
def unique_mul_inv {R : CommRing.{u}} (r : R) : is_prop (Σ (u : units R), r = u) :=
begin 
  fapply is_prop.mk, intros x y, fapply sigma_eq, 
  { hinduction x.1, hinduction y.1, 
    have H : val = val_1, from
    begin
      have p : x.1.val = val, from ap units.val _h, 
      rwr <- p, change ↑(x.1) = val_1, rwr <- x.2, 
      have q : y.1.val = val_1, from ap units.val _h_1, 
      rwr <- q, change r = ↑(y.1), rwr <- y.2
    end, 
    have H' : inv = inv_1, from 
      calc inv = inv * 1 : (comm_ring.mul_one inv)⁻¹
           ... = inv * (val_1 * inv_1) : by rwr val_inv_1
           ... = inv * (val * inv_1) : by rwr H
           ... = (inv * val) * inv_1 : (comm_ring.mul_assoc inv val inv_1)⁻¹
           ... = (val * inv) * inv_1 : ap (λ r : R, r * inv_1) (comm_ring.mul_comm inv val)
           ... = 1 * inv_1 : by rwr val_inv
           ... = inv_1 : comm_ring.one_mul inv_1, 
    fapply apd001 units.mk, 
    { exact H },
    { exact H' },
    { apply pathover_of_tr_eq, exact is_set.elim _ _ } },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end

@[hott]
def is_unit {R : CommRing} (r : R) : trunctype -1 :=
  trunctype.mk (Σ (u : units R), r = u) (unique_mul_inv r)

@[hott]
class local_ring (R : CommRing) :=
  (nontrivial : ¬ (0 = 1))
  (is_local : ∀ r : R, (is_unit r) or (is_unit (1 - r)))

/- For the constructions of limits and colimits of rings over diagrams in arbitrary universe 
   levels we need to lift the universe level of commutative rings. -/
@[hott]
def CommRing_ulift : CommRing.{u} -> CommRing.{(max u' u)} :=
begin
  intro R, fapply CommRing.mk,
  { exact trunctype_ulift R.carrier },
  { let α := comm_ring_to_ops R.str,
    fapply comm_ring_mk, 
    { fapply comm_ring_ops.mk, 
      { intros r s, exact ulift.up (α.add (ulift.down r) (ulift.down s)) }, --add
      { exact ulift.up α.zero }, --zero
      { intro r, exact ulift.up (α.neg (ulift.down r)) }, --neg
      { intros r s, exact ulift.up (α.mul (ulift.down r) (ulift.down s)) }, --mul
      { exact ulift.up α.one }, }, --one
    { fapply comm_ring_laws.mk, 
      { intros r s t, hsimp, rwr R.str.add_assoc }, --add_assoc
      { intro r, hsimp, rwr R.str.zero_add, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --zero_add
      { intro r, hsimp, rwr R.str.add_zero, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --add_zero
      { intro r, hsimp, rwr R.str.add_left_inv }, --neg_add
      { intros r s, hsimp, rwr R.str.add_comm }, --add_comm
      { intros r s t, hsimp, rwr R.str.mul_assoc }, --mul_assoc
      { intro r, hsimp, rwr R.str.one_mul, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --one_mul
      { intro r, hsimp, rwr R.str.mul_one, change ulift.up (ulift.down r) = r, 
        induction r, refl }, --mul_one
      { intros r s, hsimp, rwr R.str.mul_comm }, --mul_comm
      { intros r s t, hsimp, rwr R.str.left_distrib }, --left_distrib
      { intros r s t, hsimp, rwr R.str.right_distrib } } } --right_distrib
end    

@[hott]
def ring_ulift_functor : CommRing.{u} ⥤ CommRing.{(max u' u)} :=
begin
  fapply categories.functor.mk,
  { exact CommRing_ulift },
  { intros R S f, fapply dpair, 
    { intro r, exact ulift.up (f.1 r.down) },
    { apply prop_to_prop_resize, fapply is_ring_hom.mk, 
      { apply hott.eq.inverse, apply down_eq_up, 
        apply ((prop_resize_to_prop f.2).map_one)⁻¹ }, 
      { intros r s, apply ap ulift.up, 
        apply ((prop_resize_to_prop f.2).map_mul) }, 
      { apply hott.eq.inverse, apply down_eq_up, 
        apply ((prop_resize_to_prop f.2).map_zero)⁻¹ }, 
      { intros r s, apply ap ulift.up, 
        apply ((prop_resize_to_prop f.2).map_add) } } },
  { intro R, apply hom_eq_C_std, apply eq_of_homotopy, 
    intro r, apply hott.eq.inverse, apply down_eq_up, refl }, 
  { intros R S T f g, apply hom_eq_C_std, apply eq_of_homotopy, 
    intro r, apply hott.eq.inverse, apply down_eq_up, refl } 
end  

end algebra

end hott