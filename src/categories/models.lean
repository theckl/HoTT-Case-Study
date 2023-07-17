import categories.structures categories.boolean categories.colimits categories.pullback

universes v v' u u' w 
hott_theory

namespace hott
open signature signature.term signature.formula precategories categories.limits set 
     subset categories.colimits categories.pullbacks categories.boolean trunc

namespace categories

/- We list the properties needed to interpret particularly constructed formulas in a 
   model category, then attach these properties to the different inductive construction
   steps of formulas and finally define a class mapping each construction step to the 
   class of these properties. -/
@[hott]
inductive model_properties : Type 
| equalizer : model_properties
| pullback : model_properties
| fin_union : model_properties
| stable_image : model_properties
| all_of_fiber : model_properties
| complement : model_properties
| inf_union : model_properties
| inf_pullback : model_properties

@[hott]
def needs_properties {sign : fo_signature} (φ : formula sign) : 
  model_properties -> trunctype.{0} -1 :=
begin
  intro mp, hinduction mp, 
  { hinduction φ, exact True, exact False, exact False, exact False, 
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih,
    exact ih, exact ih, exact inf_disj ih, exact inf_disj ih }, --equalizer
  { hinduction φ, exact False, exact True, exact False, exact False, exact True, 
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact ih, exact ih, 
    exact inf_disj ih, exact inf_disj ih },                          --pullbacks
  { hinduction φ, exact False, exact False, exact False, exact True, --finite unions
    exact ih_a or ih_a_1, exact True, exact ih_a or ih_a_1, exact True, exact ih, 
    exact ih, exact inf_disj ih, exact inf_disj ih },
  { hinduction φ, exact False, exact False, exact False, exact False,  --stable images
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, 
    exact True, exact ih, exact inf_disj ih, exact inf_disj ih },
  { hinduction φ, exact False, exact False, exact False, exact False,  --all of fiber
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact True, exact True, exact ih, 
    exact True, exact inf_disj ih, exact inf_disj ih },
  { hinduction φ, exact False, exact False, exact False, exact False,  --complement
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, 
    exact ih, exact ih, exact inf_disj ih, exact inf_disj ih},  
  { hinduction φ, exact False, exact False, exact False, exact False,  --arbitrary unions
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact ih, 
    exact ih, exact inf_disj ih, exact True },
  { hinduction φ, exact False, exact False, exact False, exact False,  --arbitrary pullbacks
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact ih, 
    exact ih, exact True, exact inf_disj ih }
end     

/- An instance of this class allows to construct instances of the categorical properties
   needed to interpret formulas of a certain type. Later on, we will construct instances
   of this class from given fragments of the language. -/
@[hott]
class is_interpretable_in {sign : fo_signature} (φ : formula sign) (C : Category.{u v}) :=
(equal : needs_properties φ model_properties.equalizer -> has_equalizers C)
(pullback : needs_properties φ model_properties.pullback -> has_pullbacks C)
(fin_union : needs_properties φ model_properties.fin_union -> has_fin_unions C) 
(stable_im : needs_properties φ model_properties.stable_image -> has_pb_and_stab_im C) 
(all_fib : needs_properties φ model_properties.all_of_fiber -> has_pb_and_all_fib C)
(compl : needs_properties φ model_properties.complement -> has_pb_and_compl C)
(inf_union : needs_properties φ model_properties.inf_union -> has_unions C)
(inf_pb : needs_properties φ model_properties.inf_pullback -> has_inf_pullbacks C)

/- We need to construct instances of `is_interpretable_in` of the components of a 
   composite formula from an instance of `is_interpretable_in` of the composite formula. -/
@[hott, instance]
def interpret_conj_comp_l {sign : fo_signature} (C : Category.{u v}) (φ₁ φ₂ : formula sign) 
  [H : is_interpretable_in (formula.conj φ₁ φ₂) C] : is_interpretable_in φ₁ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inl, exact np },
  { apply pullback true.intro },
  { apply fin_union, apply or_inl, exact np },
  { apply stable_im, apply or_inl, exact np },
  { apply all_fib, apply or_inl, exact np },
  { apply compl, apply or_inl, exact np },
  { apply inf_union, apply or_inl, exact np },
  { apply inf_pb, apply or_inl, exact np },
end   

@[hott, instance]
def interpret_conj_comp_r {sign : fo_signature} (C : Category.{u v}) 
  (φ₁ φ₂ : formula sign) [H : is_interpretable_in (formula.conj φ₁ φ₂) C] : 
  is_interpretable_in φ₂ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inr, exact np },
  { apply pullback true.intro },
  { apply fin_union, apply or_inr, exact np },
  { apply stable_im, apply or_inr, exact np },
  { apply all_fib, apply or_inr, exact np },
  { apply compl, apply or_inr, exact np },
  { apply inf_union, apply or_inr, exact np },
  { apply inf_pb, apply or_inr, exact np },
end

@[hott, instance]
def interpret_disj_comp_l {sign : fo_signature} (C : Category.{u v}) (φ₁ φ₂ : formula sign) 
  [H : is_interpretable_in (formula.disj φ₁ φ₂) C] : is_interpretable_in φ₁ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inl, exact np },
  { apply pullback, apply or_inl, exact np },
  { apply fin_union true.intro },
  { apply stable_im, apply or_inl, exact np },
  { apply all_fib, apply or_inl, exact np },
  { apply compl, apply or_inl, exact np },
  { apply inf_union, apply or_inl, exact np },
  { apply inf_pb, apply or_inl, exact np },
end   

@[hott, instance]
def interpret_disj_comp_r {sign : fo_signature} (C : Category.{u v}) 
  (φ₁ φ₂ : formula sign) [H : is_interpretable_in (formula.disj φ₁ φ₂) C] : 
  is_interpretable_in φ₂ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inr, exact np },
  { apply pullback, apply or_inr, exact np },
  { apply fin_union true.intro },
  { apply stable_im, apply or_inr, exact np },
  { apply all_fib, apply or_inr, exact np },
  { apply compl, apply or_inr, exact np },
  { apply inf_union, apply or_inr, exact np },
  { apply inf_pb, apply or_inr, exact np },
end

@[hott, instance]
def interpret_impl_comp_l {sign : fo_signature} (C : Category.{u v}) 
  (φ₁ φ₂ : formula sign) [H : is_interpretable_in (formula.impl φ₁ φ₂) C] : 
  is_interpretable_in φ₁ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inl, exact np },
  { apply pullback, apply or_inl, exact np },
  { apply fin_union, apply or_inl, exact np },
  { apply stable_im, apply or_inl, exact np },
  { apply all_fib true.intro },
  { apply compl, apply or_inl, exact np },
  { apply inf_union, apply or_inl, exact np },
  { apply inf_pb, apply or_inl, exact np },
end   

@[hott, instance]
def interpret_impl_comp_r {sign : fo_signature} (C : Category.{u v}) 
  (φ₁ φ₂ : formula sign) [H : is_interpretable_in (formula.impl φ₁ φ₂) C] : 
  is_interpretable_in φ₂ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, apply or_inr, exact np },
  { apply pullback, apply or_inr, exact np },
  { apply fin_union, apply or_inr, exact np },
  { apply stable_im, apply or_inr, exact np },
  { apply all_fib true.intro },
  { apply compl, apply or_inr, exact np },
  { apply inf_union, apply or_inr, exact np },
  { apply inf_pb, apply or_inr, exact np },
end

@[hott, instance]
def interpret_neg_comp {sign : fo_signature} (C : Category.{u v}) (φ : formula sign) 
  [H : is_interpretable_in (formula.neg φ) C] : is_interpretable_in φ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, exact np },
  { apply pullback, exact np },
  { apply fin_union true.intro },
  { apply stable_im, exact np },
  { apply all_fib true.intro },
  { apply compl, exact np },
  { apply inf_union, exact np },
  { apply inf_pb, exact np },
end

@[hott, instance]
def interpret_ex_comp {sign : fo_signature} (C : Category.{u v}) 
  (v : var sign.labels sign.sorts) (φ : formula sign) 
  [H : is_interpretable_in (formula.ex v φ) C] : is_interpretable_in φ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, exact np },
  { apply pullback, exact np },
  { apply fin_union, exact np },
  { apply stable_im true.intro },
  { apply all_fib, exact np },
  { apply compl, exact np },
  { apply inf_union, exact np },
  { apply inf_pb, exact np },
end

@[hott, instance]
def interpret_univ_comp {sign : fo_signature} (C : Category.{u v}) 
  (v : var sign.labels sign.sorts) (φ : formula sign) 
  [H : is_interpretable_in (formula.univ v φ) C] : is_interpretable_in φ C :=
begin
  hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, exact np },
  { apply pullback, exact np },
  { apply fin_union, exact np },
  { apply stable_im, exact np },
  { apply all_fib true.intro },
  { apply compl, exact np },
  { apply inf_union, exact np },
  { apply inf_pb, exact np },
end

@[hott, instance]
def interpret_inf_conj_comp {sign : fo_signature} (C : Category.{u v}) 
  (i : sign.ind_Set) (φi : (sign.I i) -> formula sign) 
  [H : is_interpretable_in (formula.inf_conj φi) C] : 
  Π (j : sign.I i), is_interpretable_in (φi j) C :=
begin
  intro j, hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, exact tr ⟨j, np⟩ },
  { apply pullback, exact tr ⟨j, np⟩ },
  { apply fin_union, exact tr ⟨j, np⟩ },
  { apply stable_im, exact tr ⟨j, np⟩ },
  { apply all_fib, exact tr ⟨j, np⟩ },
  { apply compl, exact tr ⟨j, np⟩ },
  { apply inf_union, exact tr ⟨j, np⟩ },
  { apply inf_pb true.intro},
end

@[hott, instance]
def interpret_inf_disj_comp {sign : fo_signature} (C : Category.{u v}) 
  (i : sign.ind_Set) (φi : (sign.I i) -> formula sign) 
  [H : is_interpretable_in (formula.inf_disj φi) C] : 
  Π (j : sign.I i), is_interpretable_in (φi j) C :=
begin
  intro j, hinduction H,
  fapply is_interpretable_in.mk, all_goals { intro np }, 
  { apply equal, exact tr ⟨j, np⟩ },
  { apply pullback, exact tr ⟨j, np⟩ },
  { apply fin_union, exact tr ⟨j, np⟩ },
  { apply stable_im, exact tr ⟨j, np⟩ },
  { apply all_fib, exact tr ⟨j, np⟩ },
  { apply compl, exact tr ⟨j, np⟩ },
  { apply inf_union true.intro},
  { apply inf_pb, exact tr ⟨j, np⟩ },
end

@[hott]
def context_in_Sig_str {sign : fo_signature} (cont : context sign) 
  {C : Category.{u v}} [has_sign_products sign C] (Sig_str : Sig_structure sign C) : C :=
∏ (λ x : pred_Set cont.vars, Sig_str.carrier (pred_Set_map cont.vars x).sort) 

@[hott]
def cont_var_proj_in_Sig_str_hom {sign : fo_signature} (cont : context sign) 
  {J : Subset (set.to_Set (var sign.labels sign.sorts))} (inc : J ⊆ cont.vars) 
  {C : Category.{u v}} [has_sign_products sign C] (Sig_str : Sig_structure sign C) := 
  ↥((context_in_Sig_str cont Sig_str) ⟶ 
              ∏ (λ x : pred_Set J, Sig_str.carrier (pred_Set_map J x).sort))

@[hott]
def cont_var_proj_in_Sig_str {sign : fo_signature} (cont : context sign) 
  {J : Subset (set.to_Set (var sign.labels sign.sorts))} (inc : J ⊆ cont.vars) 
  {C : Category.{u v}} [has_sign_products sign C] (Sig_str : Sig_structure sign C) : 
  cont_var_proj_in_Sig_str_hom cont inc Sig_str :=
begin 
  apply pi.lift, intro j,
  change ↥(_ ⟶ Sig_str.carrier (pred_Set_map cont.vars ⟨j.1, (inc j.1 j.2)⟩).sort), 
  exact pi.π _ ⟨j.fst, inc j.fst j.snd⟩  
end

@[hott]
def interpret_of_term_hom {sign : fo_signature} {cont : context sign} 
  (tc : term_in_context cont) {C : Category.{u v}} [has_sign_products sign C] 
  (Sig_str : Sig_structure sign C) := 
  ↥((context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier (tc.t.sort)))

@[hott]
def interpret_of_term {sign : fo_signature} {cont : context sign} 
  {C : Category.{u v}} [has_sign_products sign C] (Sig_str : Sig_structure sign C) 
  (tc : term_in_context cont) : interpret_of_term_hom tc Sig_str := 
begin 
  hinduction tc, hinduction t, hinduction expr, 
  { have g : ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier x.sort), from 
      pi.π (λ x : pred_Set cont.vars, Sig_str.carrier (pred_Set_map cont.vars x).sort) 
                                                              ⟨x, in_cont x (idpath x)⟩,
    exact pv ▸[λ s', ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier s')] g },
  { let tc_args : Π (k : sign.ops_arity o), term_in_context cont := 
    begin 
      intro k, fapply term_in_context.mk,
      exact (term.mk (sign.ops_source o k) (args k)),
      exact subset_trans _ _ _ (sset_iUnion _ k) in_cont
    end, 
    have h : ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier (sign.ops_target o)), 
      from pi.lift (λ k, ih k (tc_args k).in_cont) ≫ Sig_str.str.ops o,
    exact pot ▸[λ s', ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier s')] h }
end 

@[hott]
def interpret_of_rel {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (r : sign.rels) : 
  subobject (∏ (λ a, Sig_str.carrier (@fo_signature.rels_comp sign r a))) :=
Sig_str.str.rels r

@[hott] 
def formula_subobject {sign : fo_signature} 
  (fc : formula_in_context sign) {C : Category.{u v}} [has_sign_products sign C]
  (Sig_str : Sig_structure sign C) := 
subobject (context_in_Sig_str fc.cont_of_φ.cont Sig_str)

@[hott] 
def interpret_of_equal_form {sign : fo_signature}  
  {C : Category.{u v}} [has_sign_products sign C] (Sig_str : Sig_structure sign C) 
  (t₁ t₂ : term sign) (fun_eq : t₁.sort = t₂.sort)
  (φ_cont : context_of (formula.eq_terms t₁ t₂ fun_eq)) 
  [H : is_interpretable_in (formula.eq_terms t₁ t₂ fun_eq) C] :
  formula_subobject (formula_in_context.mk (formula.eq_terms t₁ t₂ fun_eq) φ_cont) 
                    Sig_str :=
begin
  let tc₁ := term_in_context.mk t₁ (subset_trans _ _ _ (union_sset_l _ _) φ_cont.in_cont), 
  let tc₂ := term_in_context.mk t₂ (subset_trans _ _ _ (union_sset_r _ _) φ_cont.in_cont), 
  change subobject (context_in_Sig_str φ_cont.cont Sig_str),
  have p : ↥(needs_properties (formula.eq_terms t₁ t₂ fun_eq) 
                                      model_properties.equalizer), from true.intro, 
  have h : ↥((context_in_Sig_str φ_cont.cont Sig_str) ⟶ (Sig_str.carrier t₂.sort)), from 
    interpret_of_term Sig_str tc₂,
  exact @equalizer_as_subobject _ _ _ (interpret_of_term Sig_str tc₁) 
      (fun_eq⁻¹ ▸[λ s, (context_in_Sig_str φ_cont.cont Sig_str) ⟶ (Sig_str.carrier s)] h) 
      (@has_equalizer_of_has_equalizers _ _ (@is_interpretable_in.equal _ _ _ H p) 
                                        _ _ _ _)
end

@[hott]
def interpret_of_rel_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (rel : sign.rels) 
  (comp : Π (k : sign.rels_arity rel), term_of_sort (sign.rels_comp k))
  (φ_cont : context_of (formula.rel_terms rel comp))
  [H : is_interpretable_in (formula.rel_terms rel comp) C] :
  formula_subobject (formula_in_context.mk (formula.rel_terms rel comp) φ_cont) Sig_str :=
have f : ↥(context_in_Sig_str φ_cont.cont Sig_str ⟶ 
              ∏ (λ a, Sig_str.carrier (@fo_signature.rels_comp sign rel a))), from
begin 
  apply pi.lift, intro k, 
  let tc := term_in_context.mk (term.mk (sign.rels_comp k) (comp k)) 
                               (subset_trans _ _ _ (sset_iUnion _ k) φ_cont.in_cont),
  exact interpret_of_term Sig_str tc 
end,
have p : ↥(needs_properties (formula.rel_terms rel comp) 
                                      model_properties.pullback), from true.intro,
@pullback_subobject _ _ _ f (Sig_str.str.rels rel) 
          (@has_pullback_of_has_pullbacks _ _ (@is_interpretable_in.pullback _ _ _ H p)
                                          _ _ _ _ _)

@[hott]
def interpret_of_T_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C)  
  (φ_cont : context_of (formula.T sign)) [H : is_interpretable_in (formula.T sign) C] :
  formula_subobject (formula_in_context.mk (formula.T sign) φ_cont) Sig_str :=
top_subobject _

@[hott]
def interpret_of_F_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C)  
  (φ_cont : context_of (formula.F sign)) [H : is_interpretable_in (formula.F sign) C] :
  formula_subobject (formula_in_context.mk (formula.F sign) φ_cont) Sig_str :=
have p : ↥(needs_properties (formula.F sign)
                                      model_properties.fin_union), from true.intro,  
@bottom_subobject _ _ (@is_interpretable_in.fin_union _ _ _ H p)

@[hott]
def interpret_of_conj_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (φ₁ φ₂ : formula sign)
  (ih₁ : Π (φ_cont₁ : context_of φ₁) [H₁ : is_interpretable_in φ₁ C],
           formula_subobject (formula_in_context.mk φ₁ φ_cont₁) Sig_str)
  (ih₂ : Π (φ_cont₂ : context_of φ₂) [H₂ : is_interpretable_in φ₂ C],
           formula_subobject (formula_in_context.mk φ₂ φ_cont₂) Sig_str)
  (conj_cont : context_of (formula.conj φ₁ φ₂))
  [H : is_interpretable_in (formula.conj φ₁ φ₂) C] :
  formula_subobject (formula_in_context.mk (formula.conj φ₁ φ₂) conj_cont) Sig_str :=
have p : ↥(needs_properties (formula.conj φ₁ φ₂)
                                      model_properties.pullback), from true.intro,  
have Hint : has_inter (formula_subobject (formula_in_context.mk (formula.conj φ₁ φ₂) 
                                          conj_cont) Sig_str), from 
  @subobj_has_inter _ _ ((@is_interpretable_in.pullback _ _ _ H p)),  
@has_inter.inter _ Hint (@ih₁ (context_of.mk conj_cont.cont 
                               (subset_trans _ _ _ (union_sset_l _ _) conj_cont.in_cont)) 
                              (@interpret_conj_comp_l _ C φ₁ φ₂ H)) 
                        (@ih₂ (context_of.mk conj_cont.cont
                               (subset_trans _ _ _ (union_sset_r _ _) conj_cont.in_cont)) 
                              (@interpret_conj_comp_r _ C φ₁ φ₂ H))

@[hott]
def interpret_of_disj_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (φ₁ φ₂ : formula sign)
  (ih₁ : Π (φ_cont₁ : context_of φ₁) [H₁ : is_interpretable_in φ₁ C],
           formula_subobject (formula_in_context.mk φ₁ φ_cont₁) Sig_str)
  (ih₂ : Π (φ_cont₂ : context_of φ₂) [H₂ : is_interpretable_in φ₂ C],
           formula_subobject (formula_in_context.mk φ₂ φ_cont₂) Sig_str)
  (disj_cont : context_of (formula.disj φ₁ φ₂))
  [H : is_interpretable_in (formula.disj φ₁ φ₂) C] :
  formula_subobject (formula_in_context.mk (formula.disj φ₁ φ₂) disj_cont) Sig_str :=
have p : ↥(needs_properties (formula.disj φ₁ φ₂)
                                      model_properties.fin_union), from true.intro,  
have Hun : has_union (formula_subobject (formula_in_context.mk (formula.disj φ₁ φ₂) 
                                                           disj_cont) Sig_str), from 
  @subobj_has_union _ _ ((@is_interpretable_in.fin_union _ _ _ H p)),    
@has_union.union _ Hun (@ih₁ (context_of.mk disj_cont.cont
                              (subset_trans _ _ _ (union_sset_l _ _) disj_cont.in_cont)) 
                             (@interpret_disj_comp_l _ C φ₁ φ₂ H)) 
                        (@ih₂ (context_of.mk disj_cont.cont
                               (subset_trans _ _ _ (union_sset_r _ _) disj_cont.in_cont)) 
                              (@interpret_disj_comp_r _ C φ₁ φ₂ H))

@[hott]
def interpret_of_impl_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (φ₁ φ₂ : formula sign)
  (ih₁ : Π (φ_cont₁ : context_of φ₁) [H₁ : is_interpretable_in φ₁ C],
           formula_subobject (formula_in_context.mk φ₁ φ_cont₁) Sig_str)
  (ih₂ : Π (φ_cont₂ : context_of φ₂) [H₂ : is_interpretable_in φ₂ C],
           formula_subobject (formula_in_context.mk φ₂ φ_cont₂) Sig_str)
  (impl_cont : context_of (formula.impl φ₁ φ₂))
  [H : is_interpretable_in (formula.impl φ₁ φ₂) C] :
  formula_subobject (formula_in_context.mk (formula.impl φ₁ φ₂) impl_cont) Sig_str :=
have p : ↥(needs_properties (formula.impl φ₁ φ₂)
                                      model_properties.all_of_fiber), from true.intro,
have Hpbaf : has_pb_and_all_fib C, from @is_interpretable_in.all_fib _ _ _ H p, 
have Himpl : @has_implication _ Hpbaf.1.1 _ 
                      (@ih₁ (context_of.mk impl_cont.cont
                             (subset_trans _ _ _ (union_sset_l _ _) impl_cont.in_cont)) 
                            (@interpret_impl_comp_l _ C φ₁ φ₂ H))
                      (@ih₂ (context_of.mk impl_cont.cont
                             (subset_trans _ _ _ (union_sset_r _ _) impl_cont.in_cont)) 
                            (@interpret_impl_comp_r _ C φ₁ φ₂ H)), from
  @has_implication.mk _ Hpbaf.1.1 _ _ _ 
                      (@implications_of_all_fibs _ _ Hpbaf.1.1 Hpbaf.1.2 _ _),                                                                       
@impl_subobj _ Hpbaf.pb_all_fib.1 _ _ _ Himpl

@[hott]
def interpret_of_neg_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) (φ : formula sign)
  (ih : Π (φ_cont : context_of φ) [H : is_interpretable_in φ C],
          formula_subobject (formula_in_context.mk φ φ_cont) Sig_str)
  (neg_cont : context_of (formula.neg φ)) [H : is_interpretable_in (formula.neg φ) C] :
  formula_subobject (formula_in_context.mk (formula.neg φ) 
                      (context_of.mk neg_cont.cont neg_cont.in_cont)) Sig_str :=
have p : ↥(needs_properties (formula.neg φ)
                                      model_properties.all_of_fiber), from true.intro,
have Hpbaf : has_pb_and_all_fib C, from @is_interpretable_in.all_fib _ _ _ H p,
have q : ↥(needs_properties (formula.neg φ)
                                      model_properties.fin_union), from true.intro,
have Hfu : has_fin_unions C, from @is_interpretable_in.fin_union _ _ _ H q, 
have Himpl : @has_implication _ Hpbaf.1.1 _ 
                (@ih (context_of.mk neg_cont.cont neg_cont.in_cont) 
                     (@interpret_neg_comp _ C φ H))
                    (@bottom_subobject _ (context_in_Sig_str neg_cont.cont Sig_str) Hfu), from
  @has_implication.mk _ Hpbaf.1.1 _ _ _ 
                      (@implications_of_all_fibs _ _ Hpbaf.1.1 Hpbaf.1.2 _ _),                                                                       
@impl_subobj _ Hpbaf.pb_all_fib.1 _ _ _ Himpl

@[hott]
def interpret_of_ex_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) 
  (v : var sign.labels sign.sorts) (φ : formula sign) 
  (ih : Π (φ_cont : context_of φ) [H : is_interpretable_in φ C],
          formula_subobject (formula_in_context.mk φ φ_cont) Sig_str)
  (ex_cont : context_of (formula.ex v φ)) [H : is_interpretable_in (formula.ex v φ) C] :
  formula_subobject  (formula_in_context.mk (formula.ex v φ) ex_cont) Sig_str :=
begin
  have p : ↥(needs_properties (formula.ex v φ)
                                      model_properties.stable_image), from true.intro,
  let Hpb : has_pullbacks C := (@is_interpretable_in.stable_im _ _ _ H p).1.1,
  have Hsi : @has_stable_images C Hpb, from 
                                   (@is_interpretable_in.stable_im _ _ _ H p).1.2,
  have inc : ↥(formula.free_vars φ ⊆ (ex_cont.cont.vars ∪ singleton_sset v)), from 
    begin fapply set_minus_inc_impl, exact ex_cont.in_cont end,
  let cont_v : context_of φ := context_of.mk 
                                (context.mk (ex_cont.cont.vars ∪ singleton_sset v)) inc,
  let inc' := union_sset_l (ex_cont.cont.vars) (singleton_sset v),
  have Hex : @has_ex_in_fiber _ Hpb _ _ (cont_var_proj_in_Sig_str cont_v.cont inc' Sig_str), from 
    @has_ex_fib_of_has_ex_fibs _ Hpb (@has_ex_fibs_of_has_stable_ims _ Hpb Hsi) _ _ _,                                   
  change subobject _,
  exact (@ex_fib _ Hpb _ _ _ Hex).obj (@ih cont_v (@interpret_ex_comp _ C v φ H))
end

@[hott]
def interpret_of_univ_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C) 
  (v : var sign.labels sign.sorts) (φ : formula sign) 
  (ih : Π (φ_cont : context_of φ) [H : is_interpretable_in φ C],
          formula_subobject (formula_in_context.mk φ φ_cont) Sig_str)
  (univ_cont : context_of (formula.univ v φ)) 
  [H : is_interpretable_in (formula.univ v φ) C] :
  formula_subobject  (formula_in_context.mk (formula.univ v φ) univ_cont) Sig_str :=
begin
  have p : ↥(needs_properties (formula.univ v φ)
                                      model_properties.all_of_fiber), from true.intro,
  let Hpb : has_pullbacks C := (@is_interpretable_in.all_fib _ _ _ H p).1.1,
  have Haf : @has_all_of_fibers C Hpb, from 
                                   (@is_interpretable_in.all_fib _ _ _ H p).1.2,
  have inc : ↥(formula.free_vars φ ⊆ (univ_cont.cont.vars ∪ singleton_sset v)), from 
    begin fapply set_minus_inc_impl, exact univ_cont.in_cont end,
  let cont_v : context_of φ := context_of.mk 
                            (context.mk (univ_cont.cont.vars ∪ singleton_sset v)) inc,
  let inc' := union_sset_l (univ_cont.cont.vars) (singleton_sset v),
  have Hex : @has_all_of_fiber _ Hpb _ _ 
                             (cont_var_proj_in_Sig_str cont_v.cont inc' Sig_str), from 
    @has_all_fib_of_has_all_fibs _ Hpb Haf _ _ _,                                   
  exact (@fib_all _ Hpb _ _ _ Hex).obj (@ih cont_v (@interpret_univ_comp _ C v φ H))
end

@[hott]
def interpret_of_inf_conj_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C)
  (i : sign.ind_Set) (ind : (sign.I i) → formula sign)
  (ih : Π (j : sign.I i) (cont_of_φ : context_of (ind j)) 
          [H : is_interpretable_in (ind j) C],
          formula_subobject (formula_in_context.mk (ind j) cont_of_φ) Sig_str)
  (inf_conj_cont : context_of (formula.inf_conj ind))
  [H : is_interpretable_in (formula.inf_conj ind) C] :
  formula_subobject (formula_in_context.mk (formula.inf_conj ind) inf_conj_cont) 
                    Sig_str :=
begin
  have p : ↥(needs_properties (formula.inf_conj ind)
                                      model_properties.inf_pullback), from true.intro,
  have Hipb : has_inf_pullbacks C, from @is_interpretable_in.inf_pb _ _ _ H p,
  exact @subobject.union _ (context_in_Sig_str inf_conj_cont.cont Sig_str) (sign.I i) 
                 (λ j : sign.I i, @ih j (context_of.mk inf_conj_cont.cont
                  (subset_trans _ _ _ (sset_iUnion (λ j, formula.free_vars (ind j)) _) 
                 inf_conj_cont.in_cont)) (@interpret_inf_conj_comp _ _ i ind H j)) 
                 (@has_union_of_has_unions _ _ Hipb _ _)
end

@[hott]
def interpret_of_inf_disj_form {sign : fo_signature} {C : Category.{u v}} 
  [has_sign_products sign C] (Sig_str : Sig_structure sign C)
  (i : sign.ind_Set) (ind : (sign.I i) → formula sign)
  (ih : Π (j : sign.I i) (cont_of_φ : context_of (ind j)) 
          [H : is_interpretable_in (ind j) C],
          formula_subobject (formula_in_context.mk (ind j) cont_of_φ) Sig_str)
  (inf_disj_cont : context_of (formula.inf_disj ind))
  [H : is_interpretable_in (formula.inf_disj ind) C] :
  formula_subobject (formula_in_context.mk (formula.inf_disj ind) inf_disj_cont) 
                    Sig_str :=
begin
  have p : ↥(needs_properties (formula.inf_disj ind)
                                      model_properties.inf_union), from true.intro,
  have Hu : has_unions C, from @is_interpretable_in.inf_union _ _ _ H p,
  exact @subobject.union _ (context_in_Sig_str inf_disj_cont.cont Sig_str) (sign.I i) 
                 (λ j : sign.I i, @ih j (context_of.mk inf_disj_cont.cont
                  (subset_trans _ _ _ (sset_iUnion (λ j, formula.free_vars (ind j)) _) 
                 inf_disj_cont.in_cont)) (@interpret_inf_disj_comp _ _ i ind H j)) 
                 (@has_union_of_has_unions _ _ Hu _ _)
end

@[hott]
def interpret_of_form {sign : fo_signature}   
  (fc : formula_in_context sign) {C : Category.{u v}} [has_sign_products sign C]
  [H : is_interpretable_in fc.φ C] (Sig_str : Sig_structure sign C) :
  formula_subobject fc Sig_str :=
begin
  tactic.unfreeze_local_instances, hinduction fc, 
  hinduction φ with t₁ t₂ fun_eq rel comp φ₁ φ₂ ih₁ ih₂ φ₁ φ₂ ih₁ ih₂ φ₁ φ₂ ih₁ ih₂
                    φ ih v φ ih v φ ih i ind ih i ind ih,
  { exact interpret_of_equal_form Sig_str t₁ t₂ fun_eq cont_of_φ },
  { exact interpret_of_rel_form Sig_str rel comp cont_of_φ },
  { exact interpret_of_T_form Sig_str cont_of_φ },
  { exact interpret_of_F_form Sig_str cont_of_φ },
  { exact interpret_of_conj_form Sig_str φ₁ φ₂ ih₁ ih₂ cont_of_φ },
  { exact interpret_of_disj_form Sig_str φ₁ φ₂ ih₁ ih₂ cont_of_φ },
  { exact interpret_of_impl_form Sig_str φ₁ φ₂ ih₁ ih₂ cont_of_φ },
  { exact interpret_of_neg_form Sig_str φ ih cont_of_φ },
  { exact interpret_of_ex_form Sig_str v φ ih cont_of_φ },
  { exact interpret_of_univ_form Sig_str v φ ih cont_of_φ },
  { exact interpret_of_inf_conj_form Sig_str i ind ih cont_of_φ },
  { exact interpret_of_inf_disj_form Sig_str i ind ih cont_of_φ }
end    


end categories

end hott