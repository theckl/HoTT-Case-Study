import sets.algebra

--subset sets.finite sets.axioms hott.types.prod hott.types.nat.sub

universes u v w
hott_theory

namespace hott
open hott.set subset prod trunc is_trunc sum

namespace subset

/- When dealing with variables of a first-order language we need inclusion of decidable 
   subsets and their properties, and that intersections, unions and complements of 
   decidable subsets are again decidable. -/
@[hott]
def dec_inc_to_inc {S : Set} {A B : dec_Subset S} : 
  A ⊆ B -> dec_sset_to_sset A ⊆ dec_sset_to_sset B :=
begin 
  intros dec_inc x el_A, hinduction A x, 
  { change ↥(@Two.rec (λ t, Prop) _ _ _) at el_A, rwr _h at el_A, hinduction el_A },
  { change ↥(@Two.rec (λ t, Prop) _ _ _),
    have p : B x = Two.one, from dec_inc x _h, rwr p, exact true.intro } 
end

@[hott]
def inc_to_dec_inc {S : Set} {A B : dec_Subset S} : 
  dec_sset_to_sset A ⊆ dec_sset_to_sset B -> A ⊆ B :=
begin 
  intros inc x el_A, 
  have p : A x = Two.one, from el_A,
  have P : ↥(dec_sset_to_sset B x), from 
    begin apply inc x, change ↥(@Two.rec (λ t, Prop) _ _ _), rwr p, exact true.intro end, 
  change ↥(@Two.rec (λ t, Prop) _ _ _) at P, hinduction B x, rwr _h at P, hinduction P,
  exact _h 
end 

@[hott]
def dec_subset_refl {A : Set.{u}} (B : dec_Subset A) : B ⊆ B :=
  inc_to_dec_inc (subset_refl (dec_sset_to_sset B))

@[hott]
def eq_dec_subset {A : Set.{u}} (B C : dec_Subset A) : B = C -> B ⊆ C :=
  begin intro p, rwr p, exact dec_subset_refl C end 

@[hott, hsimp]
def dec_subset_trans {A : Set.{u}} (B C D : dec_Subset A) : 
  B ⊆ C -> C ⊆ D -> B ⊆ D :=
begin 
  intros BC_ss CD_ss, apply inc_to_dec_inc, 
  exact subset_trans _ _ _ (dec_inc_to_inc BC_ss) (dec_inc_to_inc CD_ss) 
end

@[hott]
def inc_inc_dec_eq {A : Set.{u}} (B C : dec_Subset A) : 
  B ⊆ C -> C ⊆ B -> B = C :=
begin
  intros inc₁ inc₂, apply dec_sset_eq_of_sset_eq _ _, 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  exact dec_inc_to_inc inc₁, exact dec_inc_to_inc inc₂
end 

@[hott, reducible]
protected def dec_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.zero t) 
                                 (λ t, Two.rec Two.zero Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_inter {A : Set.{u}} : has_inter (dec_Subset A) :=
  has_inter.mk (λ B C, hott.subset.dec_inter B C)

@[hott]
def dec_inter_is_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∩ S₂) = dec_sset_to_sset S₁ ∩ dec_sset_to_sset S₂ :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    apply pair, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
                change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) and (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc },
    all_goals { try {hinduction fst } }, all_goals { try {hinduction snd } },
    exact true.intro }
end 

@[hott]
def dec_inter_comm {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₁ ∩ S₂ = S₂ ∩ S₁ :=
begin
  apply dec_sset_eq_of_sset_eq, rwr dec_inter_is_inter, rwr dec_inter_is_inter, 
  rwr inter.symm
end

@[hott]
def inter_dec_sset_l {A : Set.{u}} (S₁ S₂ : dec_Subset A) : (S₁ ∩ S₂) ⊆ S₁ := 
  begin apply inc_to_dec_inc, rwr dec_inter_is_inter, exact inter_sset_l _ _ end

@[hott]
def inter_dec_sset_r {A : Set.{u}} (S₁ S₂ : dec_Subset A) : (S₁ ∩ S₂) ⊆ S₂ := 
  begin apply inc_to_dec_inc, rwr dec_inter_is_inter, exact inter_sset_r _ _ end


@[hott, reducible]
protected def dec_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.one t) 
                                 (λ t, Two.rec Two.one Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_union {A : Set.{u}} : has_union (dec_Subset A) :=
  has_union.mk (λ B C, hott.subset.dec_union B C)

@[hott]
def dec_union_is_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∪ S₂) = dec_sset_to_sset S₁ ∪ dec_sset_to_sset S₂ :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    all_goals { change ↥(∥ _ ∥), apply tr },  
    apply sum.inr, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro, 
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro,
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) or (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc with sum, hinduction sum },
    all_goals { try {hinduction val } }, 
    all_goals { try { exact true.intro } } }
end

@[hott]
def union_dec_sset_l {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₁ ⊆ (S₁ ∪ S₂) := 
  begin apply inc_to_dec_inc, rwr dec_union_is_union, exact union_sset_l _ _ end

@[hott]
def inc_l_dec_union {A : Set.{u}} (B S₁ S₂ : dec_Subset A) : B ⊆ S₁ -> B ⊆ (S₁ ∪ S₂) :=
  λ inc, dec_subset_trans _ _ _ inc (union_dec_sset_l _ _) 

@[hott]
def union_dec_sset_r {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₂ ⊆ (S₁ ∪ S₂) := 
  begin apply inc_to_dec_inc, rwr dec_union_is_union, exact union_sset_r _ _ end

@[hott]
def inc_r_dec_union {A : Set.{u}} (B S₁ S₂ : dec_Subset A) : B ⊆ S₂ -> B ⊆ (S₁ ∪ S₂) :=
  λ inc, dec_subset_trans _ _ _ inc (union_dec_sset_r _ _)

@[hott]
def inc_inc_dec_union_inc {A : Set.{u}} {S₁ S₂ T : dec_Subset A} : 
  S₁ ⊆ T -> S₂ ⊆ T -> (S₁ ∪ S₂) ⊆ T := 
begin
  intros inc₁ inc₂, apply inc_to_dec_inc, rwr dec_union_is_union, 
  exact inc_inc_union_inc (dec_inc_to_inc inc₁) (dec_inc_to_inc inc₂)
end 

/- Without further assumptions we can only show that finite intersections and unions of 
   decidable subsets are decidable subsets. -/
@[hott, reducible]
def dec_fin_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.one, 
  exact subset.dec_inter (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end

@[hott, instance]
def dec_ssets_have_ind_inter (A : Set.{u}) {n : ℕ} : 
  @has_ind_inter (dec_Subset A) (fin_Set n) :=
has_ind_inter.mk (λ f, @dec_fin_iInter A n f)  

@[hott]
def dec_fin_iInter_is_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋂ᵢ f) = ⋂ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
      intro m, hinduction nat.not_lt_zero m.1 m.2,
      have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p at inc, rwr dec_inter_is_inter at inc, 
      intro m, hinduction m with m q, change ↥(dec_sset_to_sset (f ⟨m, q⟩) a),
      hinduction nat.eq_sum_lt_of_le q, 
        have q : sigma.mk m q = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr q, exact inc.2, 
        have q' : m < n, from nat.lt_of_succ_lt_succ val,
        let f' := λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩,
        have r : f ⟨m, q⟩ = f' ⟨m, q'⟩, from 
        begin 
          change _ = f ⟨m, nat.le.step q'⟩, apply ap f, fapply sigma.sigma_eq,
          refl, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr r, exact ih f' inc.1 ⟨m, q'⟩ },
  { intros a inc, hinduction n,
    exact true.intro,
    have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p, rwr dec_inter_is_inter, apply pair,
    apply ih (λ (m : ↥(fin_Set n)), f ⟨m.fst, nat.le.step m.snd⟩), 
    apply prop_to_prop_resize, intro m,  
    exact prop_resize_to_prop inc ⟨m.fst, nat.le.step m.snd⟩,
    exact prop_resize_to_prop inc ⟨n, nat.le_refl (n+1)⟩ }
end

@[hott]
def dec_fin_iInter_inc {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  Π (m : fin_Set n), ⋂ᵢ f ⊆ f m :=
begin 
  intro m, apply inc_to_dec_inc, rwr dec_fin_iInter_is_iInter, exact sset_iInter _ m
end 

@[hott, reducible]
def dec_fin_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.zero, 
  exact subset.dec_union (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end                                                      

@[hott, instance]
def dec_ssets_have_fin_ind_union (A : Set.{u}) {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  @has_ind_union (dec_Subset A) (fin_Set n) f :=
has_ind_union.mk f (@dec_fin_iUnion A n f)

@[hott]
def dec_fin_iUnion_is_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋃ᵢ f) = ⋃ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
    hinduction inc,
    have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p at inc, rwr dec_union_is_union at inc,
    hinduction inc with inc, hinduction inc with inc₁ inc₂,
      hinduction ih _ inc₁ with eq₁ i_inc₁, apply tr, fapply sigma.mk, 
        exact ⟨i_inc₁.1.1, nat.le.step i_inc₁.1.2⟩, exact i_inc₁.2,
      apply tr, exact ⟨⟨n, nat.le_refl (n + 1)⟩, inc₂⟩ },
  { intros a inc, hinduction n,
      hinduction prop_resize_to_prop inc with eq i_inc, -- n=0
      hinduction nat.not_lt_zero i_inc.1.1 i_inc.1.2,      
      hinduction prop_resize_to_prop inc with eq i_inc, clear eq, -- n -> n+1
      have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p, rwr dec_union_is_union, apply tr, 
      hinduction nat.eq_sum_lt_of_le i_inc.1.2,
        apply sum.inr,                                        -- m = n
        have q : i_inc.1 = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr <- q, exact i_inc.2,
        apply sum.inl, apply ih (λ m, f ⟨m.fst, nat.le.step m.snd⟩),    -- m < n 
        apply prop_to_prop_resize, apply tr, fapply sigma.mk,
        have r : i_inc.1.1 < n, from nat.lt_of_succ_lt_succ val, 
        exact ⟨i_inc.1.1, r⟩, 
        change ↥(a∈dec_sset_to_sset (f _)), hsimp,
        have r' : i_inc.1 = ⟨i_inc.fst.fst, nat.le.step (nat.lt_of_succ_lt_succ val)⟩, from
        begin 
          hinduction i_inc.1, fapply sigma.sigma_eq, refl, 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr <- r', exact i_inc.2 }
end

@[hott]
def dec_fin_iUnion_union {A : Set.{u}} {n : ℕ} (f : fin_Set (n+1) -> dec_Subset A) :
  ⋃ᵢ f = ⋃ᵢ (λ m : fin_Set n, f (fin_Set_lift (nat.le_succ n) m)) ∪ 
                                                         (f ⟨n, nat.le_refl (n+1)⟩) :=
begin
  let f' : fin_Set (n+1) -> Powerset A := (λ m, @dec_sset_to_sset A (f m)),
  apply dec_sset_eq_of_sset_eq, rwr dec_fin_iUnion_is_iUnion, rwr dec_union_is_union,  
  rwr dec_fin_iUnion_is_iUnion, apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { apply @iUnion_sset.{u 0} A (fin_Set (n+1)) f', intro m, 
    hinduction nat.eq_sum_lt_of_le m.2, 
    { have q : m = ⟨n, nat.le_refl (n + 1)⟩, from fin_Set_eq (nat.succ.inj val),
      have p : f' m = dec_sset_to_sset (f ⟨n, nat.le_refl (n + 1)⟩), by rwr q,
      rwr p, exact union_sset_r _ _ },
    { have p : f' m = (λ (m' : fin_Set n), dec_sset_to_sset (f (fin_Set_lift 
                (nat.le_succ n) m'))) (fin_Set_desc m (nat.le_of_succ_le_succ val)), from 
        begin hsimp, apply ap dec_sset_to_sset, apply ap f, apply fin_Set_eq, refl end,
      rwr p, apply subset_trans _ _ _ _ (union_sset_l _ _), 
      exact sset_iUnion _ (fin_Set_desc m (nat.le_of_succ_le_succ val)) } },
  { apply inc_inc_union_inc, 
    { apply @iUnion_sset.{u 0} A (fin_Set n), intro m, 
      change ↥((λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) 
                                (fin_Set_lift (nat.le_succ n) m) ⊆ ⋃ᵢ _), 
      exact sset_iUnion _ (fin_Set_lift (nat.le_succ n) m) },
    { change ↥((λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) 
                                         ⟨n, nat.le_refl (n + 1)⟩ ⊆ ⋃ᵢ _), 
      apply sset_iUnion (λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) } }
end   

@[hott]
def empty_dec_iUnion_empty {A : Set.{u}} (f : fin_Set 0 -> dec_Subset A) :
  ⋃ᵢ f = empty_dec_Subset A :=
begin
  apply dec_sset_eq_of_sset_eq, rwr dec_fin_iUnion_is_iUnion,
  rwr empty_dec_sset_empty_sset, 
  have p : (⋃ᵢλ (m : ↥(fin_Set 0)), dec_sset_to_sset (f m)) = 
      ⋃ᵢ((λ (m : ↥(fin_Set 0)), dec_sset_to_sset (f m)) ∘ bij_empty_fin), from
    iUnion_index_bij (λ m, dec_sset_to_sset (f m)) bij_empty_fin,
  rwr p, exact empty_iUnion_empty _
end

@[hott]
def dec_fin_iUnion_inc {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  Π (m : fin_Set n), f m ⊆ ⋃ᵢ f :=
begin
  intro m, apply inc_to_dec_inc, rwr dec_fin_iUnion_is_iUnion, exact sset_iUnion _ m 
end  

@[hott]
def inc_dec_fin_iUnion_inc  {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A)
  (B : dec_Subset A) : (Π (m : fin_Set n), f m ⊆ B) -> ⋃ᵢ f ⊆ B :=
begin 
  intro inc_f, apply inc_to_dec_inc, rwr dec_fin_iUnion_is_iUnion, 
  apply iUnion_sset, intro m, exact dec_inc_to_inc (inc_f m)
end 

@[hott]
def inc_comp_dec_fin_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A)
  (B : dec_Subset A) : (Σ (m : fin_Set n), B ⊆ f m) -> B ⊆ ⋃ᵢ f :=
begin 
  intro inc_f_m, apply inc_to_dec_inc, rwr dec_fin_iUnion_is_iUnion, 
  apply sset_comp_iUnion, exact dpair inc_f_m.1 (dec_inc_to_inc inc_f_m.2)
end

/- If `A` has decidable equality and the underlying sets of intersection 
   and union are finite then intersection and union are decidable, since all finite 
   subsets of `A` are decidable, see [sets.finite].-/
@[hott]
def fin_iUnion_dec_sset {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  dec_Subset A :=
finite_sset_to_dec_sset.{u u u} (⋃ᵢ (λ i, dec_sset_to_sset (f i))) 

@[hott, instance]
def fin_iUnion_dec_sset_have_ind_union {A : Set.{u}} [H : decidable_eq A] {I : Set}
  (f : I -> dec_Subset A) [Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  @has_ind_union (dec_Subset A) I f :=
has_ind_union.mk f (fin_iUnion_dec_sset f)

@[hott]
def fin_iUnion_dec_sset_is_iUnion {A : Set.{u}} [decidable_eq A] {I : Set.{v}}
  (f : I -> dec_Subset A) [Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] :
  dec_sset_to_sset (⋃ᵢ f) = ⋃ᵢ (λ i : I, dec_sset_to_sset (f i)) :=
begin
  change dec_sset_to_sset (finite_sset_to_dec_sset _) = _, rwr finite_dec_sset_is_sset
end

@[hott]
def fin_iUnion_dec_sset_inc {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] :
  Π i : I, f i ⊆ (⋃ᵢ f) :=
begin
  intro i, apply inc_to_dec_inc, rwr fin_iUnion_dec_sset_is_iUnion, 
  exact sset_iUnion (λ (i : ↥I), dec_sset_to_sset (f i)) i 
end 

@[hott]
def fin_iInter_dec_sset {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋂ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  dec_Subset A :=
finite_sset_to_dec_sset (⋂ᵢ (λ i, dec_sset_to_sset (f i)))

/- The complement of a decidable subset is decidable. -/
@[hott]
protected def dec_complement {A : Set.{u}} (U : dec_Subset A) : dec_Subset A :=
  λ x : A, @Two.rec (λ t : Two, Two) Two.one Two.zero (U x) 

@[hott, instance]
def dec_sets_have_compl (A : Set) : @has_complement (dec_Subset A) :=
  has_complement.mk (λ U, subset.dec_complement U)

@[hott]
def dec_compl_is_compl {A : Set} (U : dec_Subset A) : 
  dec_sset_to_sset (𝒞 U) = 𝒞 (dec_sset_to_sset U) :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, hinduction U a with t,
    intro inc', change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc', -- U a = zero
    rwr t at inc', hinduction inc',
    have p : (𝒞 U) a = Two.zero, from           -- U a = one
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end,  
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr p at inc, hinduction inc },
  { intros a inc, hinduction U a with t, 
      have p : (𝒞 U) a = Two.one, from           -- U a = zero
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end, 
      change ↥(@Two.rec (λ t : Two, Prop) _ _ ((𝒞 U) a)), rwr p, exact true.intro, 
      have inc' : ↥(a ∈ dec_sset_to_sset U), from -- U a = one
        begin change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t, exact true.intro end,  
      hinduction inc inc' } 
end

/- The set-minus of two decidable subsets is decidable. -/
@[hott]
def dec_setminus {A : Set.{u}} (U V : dec_Subset A) : dec_Subset A :=
  λ a : A, @Two.rec (λ t : Two, Two -> Two) 
                       (λ t', @Two.rec (λ t', Two) Two.zero Two.zero (V a))
                       (λ t', @Two.rec (λ t', Two) Two.one Two.zero (V a)) (U a) (V a)

@[hott]
def dec_setminus_is_setminus {A : Set.{u}} (U V : dec_Subset A) :
  dec_sset_to_sset (dec_setminus U V) = 
                                 setminus (dec_sset_to_sset U) (dec_sset_to_sset V) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } }, apply pair, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
    intro inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr t₂ at inc, 
    hinduction inc },
  { intros a inc, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    hinduction inc with inc₁ inc₂,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc₁, 
                      rwr t₁ at inc₁, hinduction inc₁ } },
    all_goals { hsimp }, exact true.intro, 
    change ↥(Not (@Two.rec (λ t : Two, Prop) _ _ _)) at inc₂, rwr t₂ at inc₂, 
    hinduction inc₂ true.intro }
end

@[hott]
def dec_setminus_disjoint  {A : Set.{u}} (U V : dec_Subset A) : 
  V ∩ (dec_setminus U V) = empty_dec_Subset A :=
begin 
  apply dec_sset_eq_of_sset_eq, rwr dec_inter_is_inter, rwr dec_setminus_is_setminus,
  rwr empty_dec_sset_empty_sset, rwr setminus_disjoint
end

@[hott]
def dec_setminus_inc {A : Set.{u}} (U V : dec_Subset A) : dec_setminus U V ⊆ U :=
begin apply inc_to_dec_inc, rwr dec_setminus_is_setminus, exact set_minus_inc _ _ end

@[hott]
def inc_dec_setminus_inc {A : Set.{u}} (U V W : dec_Subset A) : 
  U ⊆ V -> dec_setminus U W ⊆ dec_setminus V W :=
begin 
  intros dec_ss, apply inc_to_dec_inc, rwr dec_setminus_is_setminus,
  rwr dec_setminus_is_setminus, exact inc_setminus_inc _ _ _ (dec_inc_to_inc dec_ss) 
end

@[hott]
def dec_set_minus_inc_impl {A : Set.{u}} [H : has_dec_elem A] (U V W : dec_Subset A) : 
  dec_setminus U V ⊆ W -> U ⊆ (W ∪ V) := 
begin 
  intro dec_sm_ss, apply inc_to_dec_inc, rwr dec_union_is_union,
  apply @set_minus_inc_impl _ _ _ _ H, rwr <- dec_setminus_is_setminus,
  apply dec_inc_to_inc, exact dec_sm_ss 
end

@[hott]
def dec_setminus_single_neq {A : Set.{u}} [H : decidable_eq A] {U : dec_Subset A} {a : A} 
  (el : a ∈ U) : Π (a' : A), a' ∈ dec_setminus U (singleton_dec_sset a) -> a' ≠ a :=
begin
  intros a' el' p, rwr p at el', change U a = Two.one at el, 
  change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at el', rwr el at el', 
  have p : singleton_dec_sset a a = Two.one, from singleton_dec_sset_el a,
  rwr p at el', hsimp at el', hinduction encode_Two _ _ el'
end

@[hott]
def dec_union_setminus_union {A : Set.{u}} (U V : dec_Subset A) : 
  U ∪ V = U ∪ (dec_setminus V U) :=
begin 
  apply eq_of_homotopy, intro a, 
  hinduction U a with p, all_goals { hinduction V a with q }, 
  all_goals { change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = 
    @Two.rec (λ t : Two, Two -> Two) _ _ _ (@Two.rec (λ t : Two, Two -> Two) _ _ _ _),
    rwr p, rwr q }
end

end subset

end hott