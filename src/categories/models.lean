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
def interpret_of_form {sign : fo_signature} {cont : context sign} (φ : formula sign)  
  (fc : formula_in_context φ cont) (af : is_algebraic_form φ) (C : Type u) [category.{v} C] [has_products.{v u 0} C]
  (Sig_str : Sig_structure sign C) : subobject (context_in_Sig_str cont Sig_str) :=
begin
  hinduction φ with atom T, 
  { hinduction atom with t₁ t₂ fun_eq rel,
    { have tc₁ : ↥(term_in_context t₁ cont), from sorry,
      have tc₂ : ↥(term_in_context t₂ cont), from sorry,
      sorry },
    { hinduction af } },
  { hinduction af }
end    

end categories

end hott