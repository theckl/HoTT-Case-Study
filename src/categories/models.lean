import categories.structures

universes v v' u u' w 
hott_theory

namespace hott
open signature signature.term signature.formula categories.limits subset

namespace categories

@[hott]
def context_in_Sig_str {sign : fo_signature} (cont : context sign) 
  {C : Type u} [category.{v} C] [has_products.{v u 0} C] (Sig_str : Sig_structure sign C) : C :=
∏ (λ x : pred_Set cont, Sig_str.carrier (pred_Set_map cont x).sort)   

@[hott]
def interpret_of_term {sign : fo_signature} (t : term sign) {cont : context sign} 
  (tc : term_in_context t cont) (C : Type u) [category.{v} C] [has_products.{v u 0} C] 
  (Sig_str : Sig_structure sign C) : 
  (context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier (t.sort)) := 
begin 
  hinduction t, hinduction term, 
  { have g : ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier v.sort), from 
      pi.π (λ x : pred_Set cont, Sig_str.carrier (pred_Set_map cont x).sort) ⟨v, tc v (idpath v)⟩,
    exact a ▸[λ s', ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier s')] g },
  { have tc_args : Π (k : sign.ops_arity f), term_in_context (term.mk (sign.ops_source f k) 
                                                                (args k)) cont, from
      assume k, subset_trans _ _ _ (sset_iUnion _ k) tc,
    have h : ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier (sign.ops_target f)), from
      pi.lift (λ k, ih k (tc_args k)) ≫ Sig_str.str.ops f,
    exact p ▸[λ s', ↥(context_in_Sig_str cont Sig_str ⟶ Sig_str.carrier s')] h } 
end  

@[hott]
def interpret_of_alg_form {sign : fo_signature} {cont : context sign} (φ : formula sign)  
  (fc : formula_in_context φ cont) (af : is_algebraic_form φ) (C : Type u) [category.{v} C] 
  [has_products.{v u 0} C] [has_equalizers.{v u u} C] (Sig_str : Sig_structure sign C) :
  subobject (context_in_Sig_str cont Sig_str) :=
begin
  hinduction φ with atom T, 
  { hinduction atom with t₁ t₂ fun_eq rel,
    { have tc₁ : ↥(term_in_context t₁ cont), from subset_trans _ _ _ (union_sset_l _ _) fc,
      have tc₂ : ↥(term_in_context t₂ cont), from subset_trans _ _ _ (union_sset_r _ _) fc,
      exact equalizer_as_subobject (interpret_of_term t₁ tc₁ C Sig_str) 
              (fun_eq⁻¹ ▸[λ s, (context_in_Sig_str cont Sig_str) ⟶ (Sig_str.carrier s)] 
                       (interpret_of_term t₂ tc₂ C Sig_str)) },
    { hinduction af } },
  { hinduction af }
end    

/- The category of Ω-structures on sets having a given signature is usually too large to
   capture algebraic structures: These require that particular relations involving the
   operations are true for all possible arguments. 
   
   By prescribing logical equivalences of the signature relations to such relations and
   and requesting that they are always true we can define a predicate on the objects 
   of the Ω-structure category that gives a full subcategory. 
@[hott]
structure signature_laws (sign : fo_signature) :=
  (pred : Π (S : Ω_structure sign) (r : sign.rels) 
            (args : (sign.rels_arity r) -> S.carrier), trunctype.{0} -1)
  (funct : Π {S T : Ω_structure sign} (f : S ⟶ T) (r : sign.rels) 
            (args : (sign.rels_arity r) -> S.carrier), 
            pred S r args -> pred T r (↑f ∘ args))  
  (ops_dep : Π {S T : Ω_structure sign} (f : S ⟶ T), 
               @is_set_bijective T.carrier S.carrier f -> 
               ∀ (r : sign.rels) (args : (sign.rels_arity r) -> S.carrier), 
               pred S r args <-> pred T r (↑f ∘ args))                  

@[hott]
def Ω_structure_laws_pred {sign : fo_signature} (P : signature_laws sign) : 
  Ω_structure sign -> trunctype.{0} -1 :=
begin  
intro S, 
exact prop_resize 
      (to_Prop (∀ r args, (S.str.rels r args).carrier <-> (P.pred S r args)) and
       to_Prop (∀ r args, is_true (P.pred S r args)))
end                        

@[hott]
def Ω_str_subtype {sign : fo_signature} (P : signature_laws sign) := 
  sigma.subtype (λ S : Ω_structure sign, Ω_structure_laws_pred P S)

@[hott, instance]
def Ω_str_subtype_category {sign : fo_signature} (P : signature_laws sign) : 
  category (Ω_str_subtype P) :=
full_subcat_on_subtype (Ω_structure_laws_pred P)  

/- A Subset of the underlying set of an Ω-structure inherit the structure of the 
   Ω-structure if the operations are closed on the subset. -/
@[hott]
def ops_closed {sign : fo_signature} {S : Ω_structure sign} (R : Subset S.carrier) :=
  ∀ (o : sign.ops) (args : (sign.ops_arity o) -> S.carrier), 
    (∀ i : sign.ops_arity o, args i ∈ R) -> S.str.ops o args ∈ R 

@[hott]
def str_subobject {sign : fo_signature} {S : Ω_structure sign} {R : Subset S.carrier}
  (oc : ops_closed R) : Ω_structure sign :=
begin
  fapply std_structure.mk,
  { exact pred_Set R },
  { fapply Ω_structure_on.mk, 
    { intros o x, exact ⟨S.str.ops o (sigma.fst ∘ x), oc o (sigma.fst ∘ x) (λ i, (x i).2)⟩ },
    { intros r x, exact S.str.rels r (sigma.fst ∘ x) } }
end    

/- `str_subobject` is not the only structure on a subset `R` that is closed under the 
   Ω-operations on a set `S` and is compatible with the subset embedding: There may be 
   relations on elements in `R` in the Ω-structure on `S` that do not hold in the 
   Ω-structure on `R`. But `str_subobject` is terminal among all those structures. -/
@[hott]
def str_subobject_comp {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  (std_str_of_Ω_str sign).H (str_subobject oc).str S.str (pred_Set_map R) :=
begin
  apply prop_to_prop_resize, apply is_Ω_structure_hom.mk,
  { intros o x, refl },
  { intros r x rx, exact rx }
end    

@[hott]
def terminal_str_on_subobj {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  ∀ R_str : Ω_structure_on sign (pred_Set R), 
    (std_str_of_Ω_str sign).H R_str S.str (pred_Set_map R) ->
    (std_str_of_Ω_str sign).H R_str (str_subobject oc).str (𝟙 (pred_Set R)) :=
begin
 let substr := (str_subobject oc).str, 
 intros R_str R_str_comp, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
 { intros o x, change R_str.ops o x = substr.ops o x, apply pred_Set_map_is_inj, 
   rwr (prop_resize_to_prop R_str_comp).ops_pres o x },
 { intros r x rx, change ↥(substr.rels r x), 
   exact (prop_resize_to_prop R_str_comp).rels_pres r x rx }
end                              

/- The induced structure on a subset of an Ω-structured set closed under the 
   structure operations does not necessarily satisfy the laws of a predicate if the 
   laws are satisfied by the structured set.
   
   But this is the case if the laws are left-exact. -/
@[hott]
def left_exact_sign_laws {sign : fo_signature} (P : signature_laws sign)
  {S : Ω_structure sign} (R : Subset S.1) (oc_R : ops_closed R) := Π (r : sign.rels) 
    (args : (sign.rels_arity r) -> (pred_Set R).carrier), 
    (P.pred S r ((pred_Set_map R) ∘ args) -> P.pred (str_subobject oc_R) r args)  

@[hott]
def law_str_subset {sign : fo_signature} {P : signature_laws sign} {S : Ω_str_subtype P}
  (R : Subset S.1.1) (oc_R : ops_closed R) 
  (le_laws : @left_exact_sign_laws sign P S.1 R oc_R) : 
  Ω_str_subtype P :=
begin
  fapply sigma.mk,
  { exact str_subobject oc_R },
  { change ↥(Ω_structure_laws_pred P (str_subobject oc_R)),
    apply prop_to_prop_resize, apply prod.mk, 
    { intros r args, apply prod.mk, 
      { intro so_rel, apply le_laws r args,
        apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).1, 
        assumption },
      { intro so_P, apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).2, 
        apply ((prop_resize_to_prop S.2).2 r (((pred_Set_map R)) ∘ args)).2, 
        exact true.intro } },
    { intros r args, apply prod.mk, 
      { intro so_P, exact true.intro },
      { intro t, apply le_laws r args,
        apply ((prop_resize_to_prop S.2).2 r (((pred_Set_map R)) ∘ args)).2,
        assumption } } }
end

/- Ω-structured sets have all limits because the Ω-structure on sections is induced by 
   the Ω-structure on the sets in the diagram. -/
@[hott]
def Ω_str_on_limit_cone {J : Set.{u'}} [precategory.{v'} J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : limit_cone_str_data (set_limit_cone (forget F)) :=
begin 
  fapply limit_cone_str_data.mk,
  { fapply Ω_structure_on.mk, 
    { intros o x, fapply dpair, 
      { intro j, 
        exact (F.obj j).str.ops o (((set_limit_cone (forget F)).cone.π.app j) ∘ x) },
      { apply prop_to_prop_resize, intros j k f, 
        change _ = (F.obj k).str.ops o ((set_limit_cone (forget F)).cone.π.app k ∘ x), 
        rwr <- cone.fac (set_limit_cone (forget F)).cone f, 
        exact (prop_resize_to_prop (hom_H (F.map f))).ops_pres o _ } },
    { intros r x, exact prop_resize (to_Prop (Π j : J, 
           (F.obj j).str.rels r (((set_limit_cone (forget F)).cone.π.app j) ∘ x))) } },
  { intro j, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
    { intros o x, refl },
    { intros r x limit_rel, exact prop_resize_to_prop limit_rel j } },
  { intro s, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
    { intros o x, fapply sigma.sigma_eq, 
      { apply eq_of_homotopy, intro j,
        change (s.π.app j).1 (s.X.str.ops o x) = (F.obj j).str.ops o ((s.π.app j).1 ∘ x),
        rwr (prop_resize_to_prop (s.π.app j).2).ops_pres },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intros r x s_rel, exact prop_to_prop_resize 
                (λ j : J, (prop_resize_to_prop (s.π.app j).2).rels_pres r x s_rel) } }
end

@[hott]
def Ω_str_limit_cone {J : Set.{u'}} [precategory.{v'} J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : limit_cone F :=
str_limit_cone (set_limit_cone (forget F)) (Ω_str_on_limit_cone F)  

@[hott, instance]
def Ω_str_has_limit {J : Set} [precategory J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : has_limit F :=
has_limit.mk (Ω_str_limit_cone F)

@[hott, instance]
def Ω_str_has_limits_of_shape (J : Set) [precategory J] (sign : fo_signature) : 
  has_limits_of_shape J (Ω_structure sign) :=
  has_limits_of_shape.mk (λ F, Ω_str_has_limit F)     

@[hott, instance]
def Ω_str_has_products (sign : fo_signature) : has_products (Ω_structure sign) :=
  ⟨λ J : Set, Ω_str_has_limits_of_shape (discrete J) sign⟩

@[hott, instance]
def Ω_str_has_product {J : Set} {sign : fo_signature} (f : J -> (Ω_structure sign)) : 
  has_product f :=
Ω_str_has_limit (discrete.functor f)


@[hott, instance]
def subcat_has_product {J : Set} {sign : fo_signature} (f : J -> (Ω_structure sign)) : 
  has_product f :=
Ω_str_has_limit (discrete.functor f)

/- A subtype of Ω-structures is closed under taking limits. -/
@[hott]
def Ω_str_subtype_is_limit_closed {J : Set} [precategory J] {sign : fo_signature} 
  (P : signature_laws sign) (F : J ⥤ Ω_str_subtype P) : 
  limit_closed_subtype (Ω_structure_laws_pred P) F :=
begin
  intro lc, apply prop_to_prop_resize, apply prod.mk,
  { intros r x, apply prod.mk, 
    { intro lc_rel_r_x, sorry },
    { sorry } },
  { sorry }
end  
-/

end categories

end hott