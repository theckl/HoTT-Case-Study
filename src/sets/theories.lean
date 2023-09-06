import sets.formulas

universes v v' u u' w 
hott_theory

namespace hott
open signature term formula hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv 


/- Terms and later formulas and sequents should always only contain free variables from a 
   `context`, a decidable subset of the set of variables. -/
@[hott]
structure context (sign : fo_signature) := 
  (vars : dec_Subset (to_Set (var sign.labels sign.sorts)))

@[hott]
def context_eq {sign : fo_signature} {cont₁ cont₂ : context sign} : 
  (cont₁.vars = cont₂.vars) -> (cont₁ = cont₂) :=
begin
  intro p_vars, 
  hinduction cont₁ with vars₁ pred₁, hinduction cont₂ with vars₂ pred₂,
  apply ap context.mk p_vars
end    

@[hott]
def context_eq_refl {sign : fo_signature} (cont : context sign) : 
  context_eq (@idp _ (cont.vars)) = (@idp _ cont) :=
begin 
  hinduction cont, hsimp, change ap context.mk (@idp _ vars) = _, refl
end 

@[hott]
def context_eq_eta {sign : fo_signature} {cont₁ cont₂ : context sign} (p : cont₁ = cont₂) :
  context_eq (ap context.vars p) = p := 
begin hinduction p, hsimp, exact context_eq_refl cont₁ end 

@[hott, instance]
def cont_vars_is_set {sign : fo_signature} :
  is_set ((to_Set (var sign.labels sign.sorts)) -> Two.{0}) :=
begin 
  change is_set ((var sign.labels sign.sorts) -> Two_Set), 
  exact @is_set_map _ _ 
end

@[hott, instance]
def context_is_set {sign : fo_signature} : is_set (context sign) :=
begin 
  fapply is_set.mk, intros x y p q, 
  rwr <- context_eq_eta p, rwr <- context_eq_eta q,
  apply ap context_eq, apply is_set.elim _ _, exact cont_vars_is_set
end

@[hott]
structure term_in_context {sign : fo_signature} (cont : context sign) := 
  (t : term sign) 
  (in_cont : free_vars_of_term t ⊆ cont.vars)

@[hott]
structure in_context {sign : fo_signature} (FV : free_vars sign) :=
  (cont : context sign)
  (in_cont : FV ⊆ cont.vars)

@[hott]
def in_can_context {sign : fo_signature} (FV : free_vars sign) : in_context FV :=
  in_context.mk (context.mk FV) (dec_subset_refl FV)

@[hott, reducible]
def in_context_eq {sign : fo_signature} {FV₁ FV₂ : free_vars sign} 
  {cont₁ : in_context FV₁} {cont₂ : in_context FV₂} : 
  Π (p : FV₁ = FV₂), (cont₁.cont = cont₂.cont) -> cont₁ =[p] cont₂ :=
begin
  intros pFV pc,
  hinduction cont₁ with cont₁ in_cont₁, hinduction cont₂ with cont₂ in_cont₂, 
  hinduction pFV, apply pathover_idp_of_eq, 
  fapply apd011 in_context.mk, exact pc, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end 

@[hott]
def in_context_eq_idp {sign : fo_signature} {FV : free_vars sign} 
  {cont : in_context FV} : in_context_eq (idpath FV) (idpath cont.cont) = idpo :=
begin 
  hinduction cont with cont in_cont, 
  change pathover_idp_of_eq _ _ = _,
  have q : @pathover_of_tr_eq _ (λ cont : context sign, ↥(FV⊆cont.vars)) 
             _ _ idp _ _ (is_prop.elim (idpath cont ▸ in_cont) in_cont) = idpo, from 
    is_prop.elim _ _,
  rwr q 
end

@[hott]
def form_is_in_context {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) := 
  in_context FV 

@[hott]
structure formula_in_context (sign : fo_signature) :=
  (FV : free_vars sign) 
  (φ : formula FV) 
  (cont_of_φ : in_context FV)

@[hott]
def formula_in_can_context {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :
  formula_in_context sign :=
formula_in_context.mk FV φ (in_can_context FV ) 

@[hott]
def form_cont_to_form_FV {sign : fo_signature} : 
  formula_in_context sign -> form_FV sign :=
assume φc, form_FV.mk φc.FV φc.φ 

@[hott]
def form_ext_cont {sign : fo_signature} {cont : context sign} : 
  Π (φc : formula_in_context sign), (φc.cont_of_φ.cont.vars ⊆ cont.vars) -> 
    formula_in_context sign :=
begin 
  intros φc p_cont, hinduction φc with FVφ φ φ_cont,   
  fapply formula_in_context.mk, exact FVφ, exact φ, fapply in_context.mk, exact cont, 
  apply dec_subset_trans _ _ _ φ_cont.in_cont p_cont
end

@[hott, reducible]
def formula_in_context_eq {sign : fo_signature} 
  {φc₁ φc₂ : formula_in_context sign} : 
  Π (p : φc₁.FV = φc₂.FV), φc₁.φ =[p] φc₂.φ -> φc₁.cont_of_φ.1 = φc₂.cont_of_φ.1 -> 
    φc₁ = φc₂ :=
begin 
  intros pFV pφ pc, hinduction φc₁ with FV₁ φ₁ φ_cont₁, 
  hinduction φc₂ with FV₂ φ₂ φ_cont₂, change FV₁ = FV₂ at pFV, 
  change φ₁ =[pFV] φ₂ at pφ, change φ_cont₁.cont = φ_cont₂.cont at pc, 
  fapply apd0111' formula_in_context.mk pFV pφ (in_context_eq pFV pc),  
end   

@[hott]
def formula_in_context_eq_idp {sign : fo_signature} {FV : free_vars sign} {φ : formula FV}
  {φ_cont : in_context FV} : 
  @formula_in_context_eq sign (formula_in_context.mk FV φ φ_cont) 
  (formula_in_context.mk FV φ φ_cont) (idpath FV) (idpatho φ) (idpath φ_cont.cont) = idp :=
begin change apd0111' formula_in_context.mk idp idpo _ = idp, rwr in_context_eq_idp end

@[hott]
def formula_in_context_eq_eta {sign : fo_signature} {φc₁ φc₂ : formula_in_context sign} 
  (p : φc₁ = φc₂) : formula_in_context_eq (ap formula_in_context.FV p) 
                (pathover_ap formula formula_in_context.FV (apd formula_in_context.φ p))
                        (ap (λ φc : formula_in_context sign, φc.cont_of_φ.cont) p) = p :=
begin 
  hinduction p, hsimp, rwr pathover_ap_idpo, hinduction φc₁ with FV φ φ_cont, 
  exact formula_in_context_eq_idp
end                 

@[hott, instance]
def formula_in_context_is_set {sign : fo_signature} :
  is_set (formula_in_context sign) :=
begin 
  apply is_set.mk, intros φ₁ φ₂ p q, 
  rwr <- formula_in_context_eq_eta p, rwr <- formula_in_context_eq_eta q,
    fapply apd0111' formula_in_context_eq, exact is_set.elim _ _, 
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]
structure sequent (sign : fo_signature) :=
  (ass : form_FV sign)
  (conc : form_FV sign)
  (cont : context sign)
  (in_cont : (ass.FV ∪ conc.FV) ⊆ cont.vars)

@[hott]
def seq_cont_ass {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.ass.FV, exact seq.ass.f, 
  fapply in_context.mk, exact seq.cont,
  exact dec_subset_trans _ _ _ (union_dec_sset_l _ _) seq.in_cont
end

@[hott]
def seq_cont_con {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.conc.FV, exact seq.conc.f, 
  fapply in_context.mk, exact seq.cont,
  exact dec_subset_trans _ _ _ (union_dec_sset_r _ _) seq.in_cont
end

@[hott, hsimp]
def sequent_eq {sign : fo_signature} {seq₁ seq₂ : sequent sign} :
  Π (pa : seq₁.ass = seq₂.ass) (pcc : seq₁.conc = seq₂.conc) (pct : seq₁.cont = seq₂.cont), 
    seq₁ = seq₂ :=
begin 
  intros pa pcc pct, 
  hinduction seq₁ with ass₁ conc₁ cont₁ in_cont₁, 
  hinduction seq₂ with ass₂ conc₂ cont₂ in_cont₂,
  exact apd01111_v3 sequent.mk pa pcc pct (pathover_of_tr_eq (is_prop.elim _ _))
end 

@[hott]
def sequent_eq_idp {sign : fo_signature} {seq : sequent sign} : 
  sequent_eq (ap sequent.ass (idpath seq)) (ap sequent.conc (idpath seq))
             (ap sequent.cont (idpath seq)) = idp :=
begin 
  hinduction seq with ass conc cont in_cont, rwr ap_idp, rwr ap_idp, rwr ap_idp,
  change apd01111_v3 sequent.mk idp idp idp _ = _, hsimp, refl 
end

@[hott]
def sequent_eq_eta {sign : fo_signature} {seq₁ seq₂ : sequent sign} (p : seq₁ = seq₂) :
  sequent_eq (ap sequent.ass p) (ap sequent.conc p) (ap sequent.cont p) = p := 
begin hinduction p, hinduction seq₁, exact sequent_eq_idp end 

@[hott, instance]
def sequent_is_set {sign : fo_signature} : is_set (sequent sign) :=
begin
  fapply is_set.mk, intros seq₁ seq₂ p q, 
  rwr <- sequent_eq_eta p, rwr <- sequent_eq_eta q,
  fapply ap0111' sequent_eq, exact is_set.elim _ _, exact is_set.elim _ _, 
  exact is_set.elim _ _
end 

/- We may need to introduce classes of sequents later on, if we need to invoke the class 
   mechanism. For now we just define the properties. -/

@[hott]
def sequent.horn {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.horn seq.ass.f) and (formula.horn seq.conc.f) 

@[hott]
def sequent.regular {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.regular seq.ass.f) and (formula.regular seq.conc.f) 

@[hott]
def sequent.coherent {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.coherent seq.ass.f) and (formula.coherent seq.conc.f)  

@[hott]
def sequent.first_order {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.first_order seq.ass.f) and (formula.first_order seq.conc.f)      

@[hott]
def sequent.geometric {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.geometric seq.ass.f) and (formula.geometric seq.conc.f) 

/- TODO : We need notations for formulas and sequents. -/

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

namespace theory

/- To define modules and algebras we need two sorts in an otherwise algebraic theory. So we
   drop the requirement of only one sort in an algebraic theory. -/
@[hott]
class is_algebraic {sign : fo_signature} (th : fo_theory sign) :=
  (no_rels : sign.rels = dec_fin_Set 0)
  (ass_T : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                           seq.ass = form_FV.mk (no_FV sign) formula.T)
  (conc_atom : Π seq : to_Set (sequent sign), seq ∈ th -> formula.is_atomic seq.conc.f)
  (cont_can : Π seq : to_Set (sequent sign), seq ∈ th -> seq.cont.vars = seq.conc.FV)

@[hott, instance]
def is_algebraic_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] (seq : to_Set (sequent sign)) (ax : seq ∈ th) : 
                                                  (formula.is_horn seq.ass.f) :=
begin
  let p : seq.ass.FV = no_FV sign := ap form_FV.FV (@is_algebraic.ass_T _ _ H seq ax),
  have q : seq.ass.f =[p] formula.T, from
    pathover_ap _ _ (apd form_FV.f (@is_algebraic.ass_T _ _ H seq ax)),
  have r : is_horn seq.ass.f = is_horn (@formula.T sign), from 
    apd011 (@is_horn sign) p q,
  rwr r, apply is_horn.mk, exact true.intro 
end

@[hott, instance]
def is_algebraic_th.to_con_is_atomic {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_atomic seq.conc.f) :=
assume seq ax, @is_algebraic.conc_atom _ _ H seq ax  

@[hott]
class is_horn {sign : fo_signature} (th : fo_theory sign) :=
  (horn : Π seq : to_Set (sequent sign), seq ∈ th -> 
                    (prod (formula.is_horn seq.ass.f) (formula.is_horn seq.conc.f)))

@[hott, instance]
def is_horn_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.ass.f) :=
assume seq ax, (@is_horn.horn _ _ H seq ax).1 

@[hott, instance]
def is_horn_th.to_con_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.conc.f) :=
assume seq ax, (@is_horn.horn _ _ H seq ax).2 

@[hott, instance]
def algebraic_to_horn_theory {sign : fo_signature} (th : fo_theory sign) [is_algebraic th] : 
  is_horn th := 
begin 
  apply is_horn.mk, intros seq ax, fapply pair, 
  exact is_algebraic_th.to_ass_is_horn th seq ax, 
  exact @formula.atomic.to_horn _ _ _ (is_algebraic_th.to_con_is_atomic th seq ax)  
end

@[hott]
class is_regular {sign : fo_signature} (th : fo_theory sign) :=
  (reg : Π seq : to_Set (sequent sign), seq ∈ th -> 
                (prod (formula.is_regular seq.ass.f) (formula.is_regular seq.conc.f)))

@[hott, instance]
def is_reg_th.to_ass_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.ass.f) :=
assume seq ax, (@is_regular.reg _ _ H seq ax).1 

@[hott, instance]
def is_reg_th.to_con_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.conc.f) :=
assume seq ax, (@is_regular.reg _ _ H seq ax).2 

@[hott, instance]
def horn_to_reg_theory {sign : fo_signature} (th : fo_theory sign) [is_horn th] : 
  is_regular th := 
begin 
  apply is_regular.mk, intros seq ax, fapply pair, 
  exact @formula.horn.to_regular _ _ _ (is_horn_th.to_ass_is_horn th seq ax),
  exact @formula.horn.to_regular _ _ _ (is_horn_th.to_con_is_horn th seq ax)  
end

@[hott]
class is_coherent {sign : fo_signature} (th : fo_theory sign) :=
  (coh : Π seq : to_Set (sequent sign), seq ∈ th -> 
              (prod (formula.is_coherent seq.ass.f) (formula.is_coherent seq.conc.f)))

@[hott, instance]
def is_coh_th.to_ass_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.ass.f) :=
assume seq ax, (@is_coherent.coh _ _ H seq ax).1 

@[hott, instance]
def is_coh_th.to_con_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.conc.f) :=
assume seq ax, (@is_coherent.coh _ _ H seq ax).2 

@[hott, instance]
def reg_to_coh_theory {sign : fo_signature} (th : fo_theory sign) [is_regular th] : 
  is_coherent th := 
begin 
  apply is_coherent.mk, intros seq ax, fapply pair, 
  exact @formula.regular.to_coherent _ _ _ (is_reg_th.to_ass_is_reg th seq ax),
  exact @formula.regular.to_coherent _ _ _ (is_reg_th.to_con_is_reg th seq ax)  
end

@[hott]
class is_geometric {sign : fo_signature} (th : fo_theory sign) :=
  (geom : Π seq : to_Set (sequent sign), seq ∈ th -> 
            (prod (formula.is_geometric seq.ass.f) (formula.is_geometric seq.conc.f)))

@[hott, instance]
def is_geom_th.to_ass_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.ass.f) :=
assume seq ax, (@is_geometric.geom _ _ H seq ax).1 

@[hott, instance]
def is_geom_th.to_con_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.conc.f) :=
assume seq ax, (@is_geometric.geom _ _ H seq ax).2

@[hott, instance]
def coh_to_geom_theory {sign : fo_signature} (th : fo_theory sign) [is_coherent th] : 
  is_geometric th := 
begin 
  apply is_geometric.mk, intros seq ax, fapply pair, 
  exact @formula.coherent.to_geometric _ _ _ (is_coh_th.to_ass_is_coh th seq ax),
  exact @formula.coherent.to_geometric _ _ _ (is_coh_th.to_con_is_coh th seq ax)  
end

end theory

end hott