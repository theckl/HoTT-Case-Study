import categories.structures categories.boolean categories.colimits categories.pullback

universes v v' u u' w 
hott_theory

namespace hott
open signature signature.term signature.formula precategories categories.limits subset 
     categories.colimits categories.pullbacks categories.boolean

namespace categories

/- Interpreting terms and formulas requires the construction of products in the model
   categories. Sometimes, these categories do not have arbitrary products, so it is 
   necessary to specify the kind of products which a model category of a theory must have, 
   in more details. Since all the index sets of such products are already determined by 
   the signature, namely the arity of operations and relations and the admissible 
   contexts, we can define a class listing the existence of products over all such sets. -/
@[hott]
class has_sign_products (sign : fo_signature) (C : Category) :=
  (has_arg_products : Π (o : sign.ops), has_limits_of_shape (discrete (sign.ops_arity o)) C)   
  (has_comp_products : Π (r : sign.rels), 
                                       has_limits_of_shape (discrete (sign.rels_arity r)) C)
  (has_cont_products : Π (cont : context sign), 
                                    has_limits_of_shape (discrete (pred_Set (cont.vars))) C)                                     

/- We need instances of `has_product` to construct the interpreting objects in the model 
   category deduced from `has_sign_products`. -/
@[hott, instance]
def has_term_product {sign : fo_signature} {C : Category} {o : sign.ops} 
  [H : has_sign_products sign C] (f : sign.ops_arity o -> C) : has_product f :=
@has_product_of_has_limits_of_shape _ _ _ (has_sign_products.has_arg_products C o) f

@[hott, instance]
def has_rels_product {sign : fo_signature} {C : Category} {r : sign.rels} 
  [H : has_sign_products sign C] (f : sign.rels_arity r -> C) : has_product f :=
@has_product_of_has_limits_of_shape _ _ _ (has_sign_products.has_comp_products C r) f

@[hott, instance]
def has_cont_product {sign : fo_signature} {C : Category} 
  {cont : context sign} [H : has_sign_products sign C] (f : pred_Set (cont.vars) -> C) : 
  has_product f :=
@has_product_of_has_limits_of_shape _ _ _ (has_sign_products.has_cont_products C cont) f

/- Next we list the properties needed to interpret particularly constructed formulas in a 
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
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact True, exact ih, 
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
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact True, 
    exact ih, exact ih, exact inf_disj ih, exact inf_disj ih},  
  { hinduction φ, exact False, exact False, exact False, exact False,  --arbitrary unions
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact ih, 
    exact ih, exact True, exact inf_disj ih },
  { hinduction φ, exact False, exact False, exact False, exact False,  --arbitrary pullbacks
    exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih_a or ih_a_1, exact ih, exact ih, 
    exact ih, exact inf_disj ih, exact True }
end     

/- An instance of this class allows to construct instances of the categorical properties
   needed to interpret formulas of a certain type. Later on, we will construct instances
   of this class from given fragments of the language. -/
@[hott]
class is_interpretable_in {sign : fo_signature} (φ : formula sign) (C : Category.{u v}) 
  [has_products.{v u 0} C] :=
(equal : needs_properties φ model_properties.equalizer -> has_equalizers C)
(pullback : needs_properties φ model_properties.pullback -> has_pullbacks C)
(fin_union : needs_properties φ model_properties.fin_union -> has_fin_unions C) 
(stable_im : needs_properties φ model_properties.stable_image -> has_pb_and_stab_im C) 
(all_fib : needs_properties φ model_properties.all_of_fiber -> has_pb_and_all_fib C)
(compl : needs_properties φ model_properties.complement -> has_pb_and_compl C)
(inf_union : needs_properties φ model_properties.inf_union -> has_union C)
(inf_pb : needs_properties φ model_properties.inf_pullback -> has_inf_pullbacks C)

/- We need to construct instances of `is_interpretable_in` of the components of a 
   composite formula from an instance of `is_interpretable_in` of the composite formula. -/
@[hott, instance]
def interpret_conj_comp_l {sign : fo_signature} (C : Category.{u v}) 
  [has_products.{v u 0} C] (φ₁ φ₂ : formula sign) 
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
  [has_products.{v u 0} C] (φ₁ φ₂ : formula sign) 
  [H : is_interpretable_in (formula.conj φ₁ φ₂) C] : is_interpretable_in φ₂ C :=
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
def interpret_disj_comp_l {sign : fo_signature} (C : Category.{u v}) 
  [has_products.{v u 0} C] (φ₁ φ₂ : formula sign) 
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
  [has_products.{v u 0} C] (φ₁ φ₂ : formula sign) 
  [H : is_interpretable_in (formula.disj φ₁ φ₂) C] : is_interpretable_in φ₂ C :=
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

@[hott]
def context_in_Sig_str {sign : fo_signature} (cont : context sign) 
  {C : Category.{u v}} [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) : C :=
Sig_str_prod Sig_str.str (λ x : pred_Set cont.vars, (pred_Set_map cont.vars x).sort)   

@[hott]
def interpret_of_term_hom {sign : fo_signature} {cont : context sign} 
  (tc : term_in_context cont) {C : Category.{u v}} [has_products.{v u 0} C] 
  (Sig_str : Sig_structure sign C) := 
  ↥((context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier (tc.t.sort)))

@[hott]
def interpret_of_term {sign : fo_signature} {cont : context sign} 
  {C : Category.{u v}} [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) 
  (tc : term_in_context cont) : interpret_of_term_hom tc Sig_str := 
begin 
  hinduction tc, hinduction t, hinduction expr, 
  { have g : ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier v.sort), from 
      pi.π (λ x : pred_Set cont.vars, Sig_str.carrier (pred_Set_map cont.vars x).sort) 
                                                              ⟨v, in_cont v (idpath v)⟩,
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
def interpret_of_rel {sign : fo_signature} {cont : context sign} 
  {C : Category.{u v}} [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) 
  (r : sign.rels) : 
  subobject (Sig_str_prod Sig_str.str (@fo_signature.rels_comp sign r)) :=
Sig_str.str.rels r

@[hott] 
def formula_subobject {sign : fo_signature} {cont : context sign}  
  (fc : formula_in_context cont) {C : Category.{u v}} [has_products.{v u 0} C]
  (Sig_str : Sig_structure sign C) := subobject (context_in_Sig_str cont Sig_str)

@[hott] 
def interpret_of_equal_form {sign : fo_signature} {cont : context sign}  
  {C : Category.{u v}} [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) 
  (t₁ t₂ : term sign) (fun_eq : t₁.sort = t₂.sort)
  (in_cont : formula.free_vars (formula.eq_terms t₁ t₂ fun_eq)⊆cont.vars) 
  [H : is_interpretable_in (formula.eq_terms t₁ t₂ fun_eq) C] :
  formula_subobject (formula_in_context.mk (formula.eq_terms t₁ t₂ fun_eq) in_cont) 
                    Sig_str :=
begin
  let tc₁ := term_in_context.mk t₁ (subset_trans _ _ _ (union_sset_l _ _) in_cont), 
  let tc₂ := term_in_context.mk t₂ (subset_trans _ _ _ (union_sset_r _ _) in_cont), 
  change subobject (context_in_Sig_str cont Sig_str),
  have p : ↥(needs_properties (formula.eq_terms t₁ t₂ fun_eq) 
                                      model_properties.equalizer), from true.intro, 
  have h : ↥((context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier t₂.sort)), from 
    interpret_of_term Sig_str tc₂,
  exact @equalizer_as_subobject _ _ _ (interpret_of_term Sig_str tc₁) 
      (fun_eq⁻¹ ▸[λ s, (context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier s)] h) 
      (@has_equalizer_of_has_equalizers _ _ (@is_interpretable_in.equal _ _ _ _ H p) 
                                        _ _ _ _)
end

@[hott]
def interpret_of_rel_form {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) (rel : sign.rels) 
  (comp : Π (k : sign.rels_arity rel), term_of_sort (sign.rels_comp k))
  (in_cont : formula.free_vars (formula.rel_terms rel comp)⊆cont.vars)
  [H : is_interpretable_in (formula.rel_terms rel comp) C] :
  formula_subobject (formula_in_context.mk (formula.rel_terms rel comp) in_cont) Sig_str :=
have f : ↥(context_in_Sig_str cont Sig_str ⟶ 
              (Sig_str_prod Sig_str.str (@fo_signature.rels_comp sign rel))), from
begin 
  apply pi.lift, intro k, 
  let tc := term_in_context.mk (term.mk (sign.rels_comp k) (comp k)) 
                               (subset_trans _ _ _ (sset_iUnion _ k) in_cont),
  exact interpret_of_term Sig_str tc 
end,
have p : ↥(needs_properties (formula.rel_terms rel comp) 
                                      model_properties.pullback), from true.intro,
@pullback_subobject _ _ _ f (Sig_str.str.rels rel) 
          (@has_pullback_of_has_pullbacks _ _ (@is_interpretable_in.pullback _ _ _ _ H p)
                                          _ _ _ _ _)

@[hott]
def interpret_of_T_form {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_products.{v u 0} C] (Sig_str : Sig_structure sign C)  
  (in_cont : formula.free_vars (formula.T sign)⊆cont.vars)
  [H : is_interpretable_in (formula.T sign) C] :
  formula_subobject (formula_in_context.mk (formula.T sign) in_cont) Sig_str :=
top_subobject _

@[hott]
def interpret_of_F_form {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_products.{v u 0} C] (Sig_str : Sig_structure sign C)  
  (in_cont : formula.free_vars (formula.F sign)⊆cont.vars)
  [H : is_interpretable_in (formula.F sign) C] :
  formula_subobject (formula_in_context.mk (formula.F sign) in_cont) Sig_str :=
have p : ↥(needs_properties (formula.F sign)
                                      model_properties.fin_union), from true.intro,  
@bottom_subobject _ _ (@is_interpretable_in.fin_union _ _ _ _ H p)

@[hott]
def interpret_of_conj_form {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) (φ₁ φ₂ : formula sign)
  (ih₁ : Π (in_cont₁ : formula.free_vars φ₁⊆cont.vars) [H₁ : is_interpretable_in φ₁ C],
           formula_subobject (formula_in_context.mk φ₁ in_cont₁) Sig_str)
  (ih₂ : Π (in_cont₂ : formula.free_vars φ₂⊆cont.vars) [H₂ : is_interpretable_in φ₂ C],
           formula_subobject (formula_in_context.mk φ₂ in_cont₂) Sig_str)
  (in_cont : formula.free_vars (formula.conj φ₁ φ₂)⊆cont.vars)
  [H : is_interpretable_in (formula.conj φ₁ φ₂) C] :
  formula_subobject (formula_in_context.mk (formula.conj φ₁ φ₂) in_cont) Sig_str :=
have p : ↥(needs_properties (formula.conj φ₁ φ₂)
                                      model_properties.pullback), from true.intro,  
have Hint : has_inter (formula_subobject (formula_in_context.mk (formula.conj φ₁ φ₂) 
                                            in_cont) Sig_str), from 
  @subobj_has_inter _ _ ((@is_interpretable_in.pullback _ _ _ _ H p)),  
@has_inter.inter _ Hint (@ih₁ (subset_trans _ _ _ (union_sset_l _ _) in_cont) 
                              (@interpret_conj_comp_l _ C _ φ₁ φ₂ H)) 
                        (@ih₂ (subset_trans _ _ _ (union_sset_r _ _) in_cont) 
                              (@interpret_conj_comp_r _ C _ φ₁ φ₂ H))

@[hott]
def interpret_of_disj_form {sign : fo_signature} {cont : context sign} {C : Category.{u v}} 
  [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) (φ₁ φ₂ : formula sign)
  (ih₁ : Π (in_cont₁ : formula.free_vars φ₁⊆cont.vars) [H₁ : is_interpretable_in φ₁ C],
           formula_subobject (formula_in_context.mk φ₁ in_cont₁) Sig_str)
  (ih₂ : Π (in_cont₂ : formula.free_vars φ₂⊆cont.vars) [H₂ : is_interpretable_in φ₂ C],
           formula_subobject (formula_in_context.mk φ₂ in_cont₂) Sig_str)
  (in_cont : formula.free_vars (formula.disj φ₁ φ₂)⊆cont.vars)
  [H : is_interpretable_in (formula.disj φ₁ φ₂) C] :
  formula_subobject (formula_in_context.mk (formula.disj φ₁ φ₂) in_cont) Sig_str :=
have p : ↥(needs_properties (formula.disj φ₁ φ₂)
                                      model_properties.fin_union), from true.intro,  
have Hun : has_union (formula_subobject (formula_in_context.mk (formula.disj φ₁ φ₂) 
                                            in_cont) Sig_str), from 
  @subobj_has_union _ _ ((@is_interpretable_in.fin_union _ _ _ _ H p)),    
@has_union.union _ Hun (@ih₁ (subset_trans _ _ _ (union_sset_l _ _) in_cont) 
                              (@interpret_disj_comp_l _ C _ φ₁ φ₂ H)) 
                        (@ih₂ (subset_trans _ _ _ (union_sset_r _ _) in_cont) 
                              (@interpret_disj_comp_r _ C _ φ₁ φ₂ H))

@[hott]
def interpret_of_form {sign : fo_signature} {cont : context sign}  
  (fc : formula_in_context cont) {C : Category.{u v}} [has_products.{v u 0} C]
  [H : is_interpretable_in fc.φ C] (Sig_str : Sig_structure sign C) :
  formula_subobject fc Sig_str :=
begin
  tactic.unfreeze_local_instances, hinduction fc, 
  hinduction φ with t₁ t₂ fun_eq rel comp φ₁ φ₂ ih₁ ih₂ φ₁ φ₂ ih₁ ih₂ φ₁ φ₂ ih₁ ih₂
                    φ ih v φ ih v φ ih i ind ih i ind ih,
  { exact interpret_of_equal_form Sig_str t₁ t₂ fun_eq in_cont },
  { exact interpret_of_rel_form Sig_str rel comp in_cont },
  { exact interpret_of_T_form Sig_str in_cont },
  { exact interpret_of_F_form Sig_str in_cont },
  { exact interpret_of_conj_form Sig_str φ₁ φ₂ ih₁ ih₂ in_cont },
  { exact interpret_of_disj_form Sig_str φ₁ φ₂ ih₁ ih₂ in_cont },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry }
end    


end categories

end hott