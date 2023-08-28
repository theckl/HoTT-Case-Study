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
structure context_of {sign : fo_signature} (φ : form_FV sign) :=
  (cont : context sign)
  (in_cont : form_FV.FV φ ⊆ cont.vars)

@[hott]
structure formula_in_context (sign : fo_signature) := 
  (φ : form_FV sign) 
  (cont_of_φ : context_of φ)

@[hott]
def form_ext_cont {sign : fo_signature} {cont cont': context sign} 
  (inc_cont : cont.vars ⊆ cont'.vars) : 
  Π (φc : formula_in_context sign), (φc.cont_of_φ.1 = cont) -> formula_in_context sign :=
begin 
  intros φc p_cont, hinduction φc with φ φ_cont, 
  fapply formula_in_context.mk, exact φ, fapply context_of.mk, exact cont', 
  apply subset_trans _ _ _ φ_cont.2, change φ_cont.1 = cont at p_cont, 
  rwr p_cont, exact inc_cont 
end

@[hott]
def formula_in_context_eq {sign : fo_signature} {φc₁ φc₂ : formula_in_context sign} : 
  φc₁.φ = φc₂.φ -> φc₁.cont_of_φ.1 = φc₂.cont_of_φ.1 -> φc₁ = φc₂ :=
begin 
  intros pφ pc, hinduction φc₁ with φ φ_cont, hinduction φc₂ with φ' φ_cont',
  change φ = φ' at pφ, hinduction pφ, 
  fapply apd011 formula_in_context.mk idp,  
  apply pathover_of_tr_eq, rwr idp_tr, 
  hinduction φ_cont with cont in_cont, hinduction φ_cont' with cont' in_cont',
  fapply apd011 context_of.mk pc, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end   

@[hott]
def formula_in_context_eq_eta {sign : fo_signature}
  {φ₁ φ₂ : formula_in_context sign} (p : φ₁ = φ₂) : 
  formula_in_context_eq (ap formula_in_context.φ p) 
                        (ap (λ φ : formula_in_context sign, φ.cont_of_φ.cont) p) = p :=
begin 
  hinduction p, rwr ap_idp, rwr ap_idp, hinduction φ₁ with φ φ_cont,
  hinduction φ_cont with cont in_cont, 
  change apd011 formula_in_context.mk idp _ = _,  
  hsimp, exact idp 
end                 

@[hott, instance]
def formula_in_context_is_set {sign : fo_signature} :
  is_set (formula_in_context sign) :=
begin 
  apply is_set.mk, intros φ₁ φ₂ p q, 
  rwr <- formula_in_context_eq_eta p, rwr <- formula_in_context_eq_eta q,
    fapply apd011 formula_in_context_eq, exact is_set.elim _ _, 
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end

@[hott]
structure sequent (sign : fo_signature) :=
  (ass : formula_in_context sign)
  (con : formula_in_context sign)

@[hott]
def seq_context {sign : fo_signature} (seq : sequent sign) : context sign := 
  context.mk (seq.ass.cont_of_φ.cont.vars ∪ seq.con.cont_of_φ.cont.vars)

@[hott]
def seq_cont_ass {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.ass.φ, 
  fapply context_of.mk, exact seq_context seq,
  exact dec_subset_trans _ _ _ (formula_in_context.cont_of_φ seq.ass).in_cont 
                           (union_dec_sset_l _ _)
end

@[hott]
def seq_cont_con {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.con.φ, 
  fapply context_of.mk, exact seq_context seq,
  exact dec_subset_trans _ _ _ (formula_in_context.cont_of_φ seq.con).in_cont 
                           (union_dec_sset_r _ _)
end

@[hott, hsimp]
def sequent_eq {sign : fo_signature} {seq₁ seq₂ : sequent sign} :
  Π (pa : seq₁.ass = seq₂.ass) (pc : seq₁.con = seq₂.con), seq₁ = seq₂ :=
begin 
  intros pa pc, 
  hinduction seq₁ with ass con, hinduction seq₂ with ass' con', 
  exact ap011 sequent.mk pa pc
end 

@[hott]
def sequent_eq_eta {sign : fo_signature} {seq₁ seq₂ : sequent sign} (p : seq₁ = seq₂) :
  sequent_eq (ap sequent.ass p) (ap sequent.con p) = p := 
begin hinduction p, hinduction seq₁, exact idp end 

@[hott, instance]
def sequent_is_set {sign : fo_signature} : is_set (sequent sign) :=
begin
  fapply is_set.mk, intros seq₁ seq₂ p q, 
  rwr <- sequent_eq_eta p, rwr <- sequent_eq_eta q,
  fapply ap011 sequent_eq, exact is_set.elim _ _, exact is_set.elim _ _
end 

/- We may need to introduce classes of sequents later on, if we need to invoke the class 
   mechanism. For now we just define the properties. -/

@[hott]
def sequent.horn {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.horn seq.ass.φ.f) and (formula.horn seq.con.φ.f) 

@[hott]
def sequent.regular {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.regular seq.ass.φ.f) and (formula.regular seq.con.φ.f) 

@[hott]
def sequent.coherent {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.coherent seq.ass.φ.f) and (formula.coherent seq.con.φ.f)  

@[hott]
def sequent.first_order {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.first_order seq.ass.φ.f) and (formula.first_order seq.con.φ.f)      

@[hott]
def sequent.geometric {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.geometric seq.ass.φ.f) and (formula.geometric seq.con.φ.f) 

/- TODO : We need notations for formulas and sequents. -/

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

namespace theory

/- To define modules and algebras we need two sorts in an otherwise algebraic theory. So we
   drop the requirement of only one sort in an algebraic theory. -/
@[hott]
class is_algebraic {sign : fo_signature} (th : fo_theory sign) :=
  (alg : prod (fin_Set 0 ≃ sign.rels) (Π seq : to_Set (sequent sign), seq ∈ th -> 
                  (prod (seq.ass.φ = form_FV.mk (no_FV sign) formula.T)) 
                        (formula.is_atomic seq.con.φ.f)))

@[hott, instance]
def is_algebraic_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] (seq : to_Set (sequent sign)) (ax : seq ∈ th) : 
                                                  (formula.is_horn seq.ass.φ.f) :=
begin rwr (H.alg.2 seq ax).1, apply is_horn.mk, exact true.intro end

@[hott, instance]
def is_algebraic_th.to_con_is_atomic {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_atomic seq.con.φ.f) :=
assume seq ax, (H.alg.2 seq ax).2  

@[hott]
class is_horn {sign : fo_signature} (th : fo_theory sign) :=
  (horn : Π seq : to_Set (sequent sign), seq ∈ th -> 
                    (prod (formula.is_horn seq.ass.φ.f) (formula.is_horn seq.con.φ.f)))

@[hott, instance]
def is_horn_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.ass.φ.f) :=
assume seq ax, (@is_horn.horn _ _ H seq ax).1 

@[hott, instance]
def is_horn_th.to_con_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.con.φ.f) :=
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
                (prod (formula.is_regular seq.ass.φ.f) (formula.is_regular seq.con.φ.f)))

@[hott, instance]
def is_reg_th.to_ass_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.ass.φ.f) :=
assume seq ax, (@is_regular.reg _ _ H seq ax).1 

@[hott, instance]
def is_reg_th.to_con_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.con.φ.f) :=
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
              (prod (formula.is_coherent seq.ass.φ.f) (formula.is_coherent seq.con.φ.f)))

@[hott, instance]
def is_coh_th.to_ass_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.ass.φ.f) :=
assume seq ax, (@is_coherent.coh _ _ H seq ax).1 

@[hott, instance]
def is_coh_th.to_con_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.con.φ.f) :=
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
            (prod (formula.is_geometric seq.ass.φ.f) (formula.is_geometric seq.con.φ.f)))

@[hott, instance]
def is_geom_th.to_ass_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.ass.φ.f) :=
assume seq ax, (@is_geometric.geom _ _ H seq ax).1 

@[hott, instance]
def is_geom_th.to_con_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.con.φ.f) :=
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