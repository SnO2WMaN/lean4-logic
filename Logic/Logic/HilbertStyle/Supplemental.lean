import Logic.Logic.System
import Logic.Logic.HilbertStyle.Context

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
         {S : Type*} [System F S]
         {𝓢 : S}
         [Minimal 𝓢]
         {p q r : F}
         {Γ Δ : List F}

open FiniteContext


def bot_of_mem_either (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  exact (by simpa [NegDefinition.neg] using FiniteContext.byAxm h₂) ⨀ (FiniteContext.byAxm h₁);
@[simp] lemma bot_of_mem_either! (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩


def efq_of_mem_either [HasEFQ 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢] q := efq' $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [HasEFQ 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢]! q := ⟨efq_of_mem_either h₁ h₂⟩

lemma efq_of_neg! [HasEFQ 𝓢] (h : 𝓢 ⊢! ~p) : 𝓢 ⊢! p ⟶ q := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [p] ⊢[𝓢]! p ⟶ ⊥ := by simpa [NegDefinition.neg] using of'! h;
  have dp : [p] ⊢[𝓢]! p := by_axm! (by simp);
  exact efq'! (dnp ⨀ dp);


lemma orComm : 𝓢 ⊢ p ⋎ q ⟶ q ⋎ p := by
  apply deduct';
  exact disj₃' disj₂ disj₁ $ FiniteContext.byAxm (by simp);
lemma orComm! : 𝓢 ⊢! p ⋎ q ⟶ q ⋎ p := ⟨orComm⟩

lemma orComm' (h : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ q ⋎ p := orComm ⨀ h
lemma orComm'! (h : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! q ⋎ p := ⟨orComm' h.some⟩

def implyRightAnd (hq : 𝓢 ⊢ p ⟶ q) (hr : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ q ⋏ r := by
  apply deduct';
  replace hq : [] ⊢[𝓢] p ⟶ q := of hq;
  replace hr : [] ⊢[𝓢] p ⟶ r := of hr;
  exact conj₃' (mdp' hq (FiniteContext.byAxm (by simp))) (mdp' hr (FiniteContext.byAxm (by simp)))
@[simp] lemma implyRightAnd! (hq : 𝓢 ⊢! p ⟶ q) (hr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ q ⋏ r := ⟨implyRightAnd hq.some hr.some⟩


def andReplaceLeft' (hc : 𝓢 ⊢ p ⋏ q) (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ r ⋏ q := conj₃' (h ⨀ conj₁' hc) (conj₂' hc)
lemma andReplaceLeft'! (hc : 𝓢 ⊢! p ⋏ q) (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! r ⋏ q := ⟨andReplaceLeft' hc.some h.some⟩

def andReplaceLeft (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⋏ q ⟶ r ⋏ q := by
  apply deduct';
  exact andReplaceLeft' (FiniteContext.byAxm (by simp)) (of h)
lemma andReplaceLeft! (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⋏ q ⟶ r ⋏ q := ⟨andReplaceLeft h.some⟩


def andReplaceRight' (hc : 𝓢 ⊢ p ⋏ q) (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋏ r := conj₃' (conj₁' hc) (h ⨀ conj₂' hc)
lemma andReplaceRight'! (hc : 𝓢 ⊢! p ⋏ q) (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋏ r := ⟨andReplaceRight' hc.some h.some⟩

def andReplaceRight (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋏ q ⟶ p ⋏ r := by
  apply deduct';
  exact andReplaceRight' (FiniteContext.byAxm (by simp)) (of h)
lemma andReplaceRight! (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋏ q ⟶ p ⋏ r := ⟨andReplaceRight h.some⟩


def andReplace' (hc : 𝓢 ⊢ p ⋏ q) (h₁ : 𝓢 ⊢ p ⟶ r) (h₂ : 𝓢 ⊢ q ⟶ s) : 𝓢 ⊢ r ⋏ s := andReplaceRight' (andReplaceLeft' hc h₁) h₂
lemma andReplace'! (hc : 𝓢 ⊢! p ⋏ q) (h₁ : 𝓢 ⊢! p ⟶ r) (h₂ : 𝓢 ⊢! q ⟶ s) : 𝓢 ⊢! r ⋏ s := ⟨andReplace' hc.some h₁.some h₂.some⟩

def andReplace (h₁ : 𝓢 ⊢ p ⟶ r) (h₂ : 𝓢 ⊢ q ⟶ s) : 𝓢 ⊢ p ⋏ q ⟶ r ⋏ s := by
  apply deduct';
  exact andReplace' (FiniteContext.byAxm (by simp)) (of h₁) (of h₂)
lemma andReplace! (h₁ : 𝓢 ⊢! p ⟶ r) (h₂ : 𝓢 ⊢! q ⟶ s) : 𝓢 ⊢! p ⋏ q ⟶ r ⋏ s := ⟨andReplace h₁.some h₂.some⟩


def orReplaceLeft' (hc : 𝓢 ⊢ p ⋎ q) (hp : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ r ⋎ q := disj₃' (impTrans hp disj₁) (disj₂) hc
lemma or_replace_left'! (hc : 𝓢 ⊢! p ⋎ q) (hp : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! r ⋎ q := ⟨orReplaceLeft' hc.some hp.some⟩

def orReplaceLeft (hp : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⋎ q ⟶ r ⋎ q := by
  apply deduct';
  exact orReplaceLeft' (FiniteContext.byAxm (by simp)) (of hp)
lemma or_replace_left! (hp : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⋎ q ⟶ r ⋎ q := ⟨orReplaceLeft hp.some⟩


def orReplaceRight' (hc : 𝓢 ⊢ p ⋎ q) (hq : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋎ r := disj₃' (disj₁) (impTrans hq disj₂) hc
lemma or_replace_right'! (hc : 𝓢 ⊢! p ⋎ q) (hq : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋎ r := ⟨orReplaceRight' hc.some hq.some⟩

def orReplaceRight (hq : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋎ q ⟶ p ⋎ r := by
  apply deduct';
  exact orReplaceRight' (FiniteContext.byAxm (by simp)) (of hq)
lemma or_replace_right! (hq : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋎ q ⟶ p ⋎ r := ⟨orReplaceRight hq.some⟩


def orReplace' (h : 𝓢 ⊢ p₁ ⋎ q₁) (hp : 𝓢 ⊢ p₁ ⟶ p₂) (hq : 𝓢 ⊢ q₁ ⟶ q₂) : 𝓢 ⊢ p₂ ⋎ q₂ := orReplaceRight' (orReplaceLeft' h hp) hq
lemma or_replace'! (h : 𝓢 ⊢! p₁ ⋎ q₁) (hp : 𝓢 ⊢! p₁ ⟶ p₂) (hq : 𝓢 ⊢! q₁ ⟶ q₂) : 𝓢 ⊢! p₂ ⋎ q₂ := ⟨orReplace' h.some hp.some hq.some⟩

def orReplace (hp : 𝓢 ⊢ p₁ ⟶ p₂) (hq : 𝓢 ⊢ q₁ ⟶ q₂) : 𝓢 ⊢ p₁ ⋎ q₁ ⟶ p₂ ⋎ q₂ := by
  apply deduct';
  exact orReplace' (FiniteContext.byAxm (by simp)) (of hp) (of hq) ;
lemma or_replace! (hp : 𝓢 ⊢! p₁ ⟶ p₂) (hq : 𝓢 ⊢! q₁ ⟶ q₂) : 𝓢 ⊢! p₁ ⋎ q₁ ⟶ p₂ ⋎ q₂ := ⟨orReplace hp.some hq.some⟩


def dni : 𝓢 ⊢ p ⟶ ~~p := by
  rw [NegDefinition.neg];
  apply deduct';
  apply deduct;
  exact bot_of_mem_either (p := p) (by simp) (by simp);
@[simp] lemma dni! : 𝓢 ⊢! p ⟶ ~~p := ⟨dni⟩

def dni' (b : 𝓢 ⊢ p) : 𝓢 ⊢ ~~p := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! p) : 𝓢 ⊢! ~~p := ⟨dni' b.some⟩


def dniOr' (d : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ ~~p ⋎ ~~q := disj₃' (impTrans dni disj₁) (impTrans dni disj₂) d
@[simp] lemma dniOr'! (d : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! ~~p ⋎ ~~q := ⟨dniOr' d.some⟩

def dniAnd' (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ ~~p ⋏ ~~q := conj₃' (dni' $ conj₁' d) (dni' $ conj₂' d)
@[simp] lemma dniAnd'! (d : 𝓢 ⊢! p ⋏ q) : 𝓢 ⊢! ~~p ⋏ ~~q := ⟨dniAnd' d.some⟩


def dn [HasDNE 𝓢] : 𝓢 ⊢ p ⟷ ~~p := iffIntro dni dne
@[simp] lemma dn! [HasDNE 𝓢] : 𝓢 ⊢! p ⟷ ~~p := ⟨dn⟩


def contra₀ : 𝓢 ⊢ (p ⟶ q) ⟶ (~q ⟶ ~p) := by
  simp [NegDefinition.neg];
  apply deduct';
  apply deduct;
  apply deduct;
  have d₁ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] p := FiniteContext.byAxm (by simp);
  have d₂ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] q ⟶ ⊥ := FiniteContext.byAxm (by simp);
  have d₃ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] p ⟶ q := FiniteContext.byAxm (by simp);
  exact d₂ ⨀ (d₃ ⨀ d₁);
@[simp] def contra₀! : 𝓢 ⊢! (p ⟶ q) ⟶ (~q ⟶ ~p) := ⟨contra₀⟩

def contra₀' (b : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~q ⟶ ~p := contra₀ ⨀ b
@[simp] lemma contra₀'! (b : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~q ⟶ ~p := ⟨contra₀' b.some⟩


def contra₀x2' (b : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~~p ⟶ ~~q := contra₀' $ contra₀' b
@[simp] lemma contra₀x2'! (b : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~~p ⟶ ~~q := ⟨contra₀x2' b.some⟩

def contra₀x2 : 𝓢 ⊢ (p ⟶ q) ⟶ (~~p ⟶ ~~q) := by
  apply deduct';
  exact contra₀x2' $ FiniteContext.byAxm (by simp only [List.mem_singleton]);
@[simp] lemma contra₀x2! : 𝓢 ⊢! (p ⟶ q) ⟶ (~~p ⟶ ~~q) := ⟨contra₀x2⟩


def contra₁' (b : 𝓢 ⊢ p ⟶ ~q) : 𝓢 ⊢ q ⟶ ~p := impTrans dni (contra₀' b)
@[simp] lemma contra₁'! (b : 𝓢 ⊢! p ⟶ ~q) : 𝓢 ⊢! q ⟶ ~p := ⟨contra₁' b.some⟩

def contra₁ : 𝓢 ⊢ (p ⟶ ~q) ⟶ (q ⟶ ~p) := by
  apply deduct';
  exact contra₁' $ FiniteContext.byAxm (by simp);
@[simp] lemma contra₁! : 𝓢 ⊢! (p ⟶ ~q) ⟶ (q ⟶ ~p) := ⟨contra₁⟩


def contra₂' [HasDNE 𝓢] (b : 𝓢 ⊢ ~p ⟶ q) : 𝓢 ⊢ ~q ⟶ p := impTrans (contra₀' b) dne
@[simp] lemma contra₂'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~p ⟶ q) : 𝓢 ⊢! ~q ⟶ p := ⟨contra₂' b.some⟩

def contra₂ [HasDNE 𝓢] : 𝓢 ⊢ (~p ⟶ q) ⟶ (~q ⟶ p) := by
  apply deduct';
  exact contra₂' $ FiniteContext.byAxm (by simp);
@[simp] lemma contra₂! [HasDNE 𝓢] : 𝓢 ⊢! (~p ⟶ q) ⟶ (~q ⟶ p) := ⟨contra₂⟩


def contra₃' [HasDNE 𝓢] (b : 𝓢 ⊢ ~p ⟶ ~q) : 𝓢 ⊢ q ⟶ p := impTrans dni (contra₂' b)
@[simp] lemma contra₃'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~p ⟶ ~q) : 𝓢 ⊢! q ⟶ p := ⟨contra₃' b.some⟩

def contra₃ [HasDNE 𝓢] : 𝓢 ⊢ (~p ⟶ ~q) ⟶ (q ⟶ p) := by
  apply deduct';
  exact contra₃' $ FiniteContext.byAxm (by simp);
@[simp] lemma contra₃! [HasDNE 𝓢] : 𝓢 ⊢! (~p ⟶ ~q) ⟶ (q ⟶ p) := ⟨contra₃⟩


def neg_iff' (b : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ ~p ⟷ ~q := iffIntro (contra₀' $ conj₂' b) (contra₀' $ conj₁' b)
lemma neg_iff'! (b : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ~p ⟷ ~q := ⟨neg_iff' b.some⟩


def tne : 𝓢 ⊢ ~(~~p) ⟶ ~p := contra₀' dni
@[simp] lemma tne! : 𝓢 ⊢! ~(~~p) ⟶ ~p := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ~(~~p)) : 𝓢 ⊢ ~p := tne ⨀ b
@[simp] lemma tne'! (b : 𝓢 ⊢! ~(~~p)) : 𝓢 ⊢! ~p := ⟨tne' b.some⟩


lemma implyLeftReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  constructor;
  . exact imp_trans! $ conj₂'! h;
  . exact imp_trans! $ conj₁'! h;


lemma implyRightReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  constructor;
  . intro hrp; exact imp_trans! hrp $ conj₁'! h;
  . intro hrq; exact imp_trans! hrq $ conj₂'! h;


def impSwap' (h : 𝓢 ⊢ p ⟶ q ⟶ r) : 𝓢 ⊢ q ⟶ p ⟶ r := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [p, q]) h) ⨀ FiniteContext.byAxm (by simp) ⨀ FiniteContext.byAxm (by simp);
@[simp] lemma imp_swap'! (h : 𝓢 ⊢! (p ⟶ q ⟶ r)) : 𝓢 ⊢! (q ⟶ p ⟶ r) := ⟨impSwap' h.some⟩

def impSwap : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (q ⟶ p ⟶ r) := by
  apply deduct';
  exact impSwap' $ FiniteContext.byAxm (by simp);
@[simp] lemma imp_swap! : 𝓢 ⊢! (p ⟶ q ⟶ r) ⟶ (q ⟶ p ⟶ r) := ⟨impSwap⟩


-- TODO: Too Slow
def dnDistributeImply : 𝓢 ⊢ ~~(p ⟶ q) ⟶ (~~p ⟶ ~~q) := by
  apply impSwap';
  apply deduct';
  exact impTrans (contra₀x2' $ deductInv $ of $ impSwap' $ contra₀x2) tne;
@[simp] lemma dn_distribute_imply! : 𝓢 ⊢! ~~(p ⟶ q) ⟶ (~~p ⟶ ~~q) := ⟨dnDistributeImply⟩

def dnDistributeImply' (b : 𝓢 ⊢ ~~(p ⟶ q)) : 𝓢 ⊢ ~~p ⟶ ~~q := dnDistributeImply ⨀ b
@[simp] lemma dn_distribute_imply'! (b : 𝓢 ⊢! ~~(p ⟶ q)) : 𝓢 ⊢! ~~p ⟶ ~~q := ⟨dnDistributeImply' b.some⟩


def introFalsumOfAnd' (h : 𝓢 ⊢ p ⋏ ~p) : 𝓢 ⊢ ⊥ := by
  simp [NegDefinition.neg] at h;
  exact (conj₂' h) ⨀ (conj₁' h)
@[simp] lemma introFalsumOfAnd'! (h : 𝓢 ⊢! p ⋏ ~p) : 𝓢 ⊢! ⊥ := ⟨introFalsumOfAnd' h.some⟩

def introFalsumOfAnd : 𝓢 ⊢ p ⋏ ~p ⟶ ⊥ := by
  apply deduct';
  exact introFalsumOfAnd' (p := p) $ FiniteContext.byAxm (by simp);
@[simp] lemma introFalsumOfAnd! : 𝓢 ⊢! p ⋏ ~p ⟶ ⊥ := ⟨introFalsumOfAnd⟩



def implyOfNotOr [HasEFQ 𝓢] : 𝓢 ⊢ (~p ⋎ q) ⟶ (p ⟶ q) := disj₃'' (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (p := p) (by simp) (by simp)
  ) imply₁
@[simp] lemma implyOfNotOr! [HasEFQ 𝓢] : 𝓢 ⊢! (~p ⋎ q) ⟶ (p ⟶ q) := ⟨implyOfNotOr⟩

def implyOfNotOr' [HasEFQ 𝓢] (b : 𝓢 ⊢ ~p ⋎ q) : 𝓢 ⊢ p ⟶ q := implyOfNotOr ⨀ b
@[simp] lemma implyOfNotOr'! [HasEFQ 𝓢] (b : 𝓢 ⊢! ~p ⋎ q) : 𝓢 ⊢! p ⟶ q := ⟨implyOfNotOr' b.some⟩


def demorgan₁ : 𝓢 ⊢ (~p ⋎ ~q) ⟶ ~(p ⋏ q) := disj₃'' (contra₀' conj₁) (contra₀' conj₂)
@[simp] lemma demorgan₁! : 𝓢 ⊢! (~p ⋎ ~q) ⟶ ~(p ⋏ q) := ⟨demorgan₁⟩

def demorgan₁' (d : 𝓢 ⊢ ~p ⋎ ~q) : 𝓢 ⊢ ~(p ⋏ q)  := demorgan₁ ⨀ d
@[simp] lemma demorgan₁'! (d : 𝓢 ⊢! ~p ⋎ ~q) : 𝓢 ⊢! ~(p ⋏ q) := ⟨demorgan₁' d.some⟩


def demorgan₂ : 𝓢 ⊢ (~p ⋏ ~q) ⟶ ~(p ⋎ q) := by
  simp [NegDefinition.neg];
  apply deduct';
  exact disj₃'' (conj₁' (q := q ⟶ ⊥) $ FiniteContext.byAxm (by simp)) (conj₂' (p := p ⟶ ⊥) $ FiniteContext.byAxm (by simp))
@[simp] lemma demorgan₂! : 𝓢 ⊢! ~p ⋏ ~q ⟶ ~(p ⋎ q) := ⟨demorgan₂⟩

def demorgan₂' (d : 𝓢 ⊢ ~p ⋏ ~q) : 𝓢 ⊢ ~(p ⋎ q) := demorgan₂ ⨀ d
@[simp] lemma demorgan₂'! (d : 𝓢 ⊢! ~p ⋏ ~q) : 𝓢 ⊢! ~(p ⋎ q) := ⟨demorgan₂' d.some⟩


-- TODO: Too Slow
def demorgan₃ : 𝓢 ⊢ ~(p ⋎ q) ⟶ (~p ⋏ ~q) := by
  apply deduct';
  exact conj₃' (deductInv $ contra₀' $ disj₁) (deductInv $ contra₀' $ disj₂)
@[simp] lemma demorgan₃! : 𝓢 ⊢! ~(p ⋎ q) ⟶ (~p ⋏ ~q) := ⟨demorgan₃⟩

def demorgan₃' (b : 𝓢 ⊢ ~(p ⋎ q)) : 𝓢 ⊢ ~p ⋏ ~q := demorgan₃ ⨀ b
@[simp] lemma demorgan₃'! (b : 𝓢 ⊢! ~(p ⋎ q)) : 𝓢 ⊢! ~p ⋏ ~q := ⟨demorgan₃' b.some⟩


-- TODO: Too Slow
def demorgan₄ [HasDNE 𝓢] : 𝓢 ⊢ ~(p ⋏ q) ⟶ (~p ⋎ ~q) := by
  apply contra₂';
  apply deduct';
  have : [~(~p ⋎ ~q)] ⊢[𝓢] ~~p ⋏ ~~q := demorgan₃' $ FiniteContext.byAxm (by simp);
  exact andReplace' this dne dne;
@[simp] lemma demorgan₄! [HasDNE 𝓢] : 𝓢 ⊢! ~(p ⋏ q) ⟶ (~p ⋎ ~q) := ⟨demorgan₄⟩

def demorgan₄' [HasDNE 𝓢] (b : 𝓢 ⊢ ~(p ⋏ q)) : 𝓢 ⊢ ~p ⋎ ~q := demorgan₄ ⨀ b
@[simp] lemma demorgan₄'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~(p ⋏ q)) : 𝓢 ⊢! ~p ⋎ ~q := ⟨demorgan₄' b.some⟩

-- TODO: Too Slow
set_option trace.profiler true in
def NotOrOfImply' [HasDNE 𝓢] (d : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~p ⋎ q := by
  apply dne';
  rw [NegDefinition.neg];
  apply deduct';
  have d₁ : [~(~p ⋎ q)] ⊢[𝓢] ~~p ⋏ ~q := demorgan₃' $ FiniteContext.byAxm (by simp);
  have d₂ : [~(~p ⋎ q)] ⊢[𝓢] ~p ⟶ ⊥ := by simpa only [NegDefinition.neg] using conj₁' d₁;
  have d₃ : [~(~p ⋎ q)] ⊢[𝓢] ~p := (of (Γ := [~(~p ⋎ q)]) $ contra₀' d) ⨀ (conj₂' d₁);
  exact d₂ ⨀ d₃;
@[simp] lemma NotOrOfImply'! [HasDNE 𝓢] (d : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~p ⋎ q := ⟨NotOrOfImply' d.some⟩

-- TODO: Too Slow
set_option trace.profiler true in
def dnCollectImply [HasEFQ 𝓢] : 𝓢 ⊢ (~~p ⟶ ~~q) ⟶ ~~(p ⟶ q) := by
  apply deduct';
  nth_rw 5 [NegDefinition.neg];
  exact impTrans
    (by
      apply deductInv;
      apply andImplyIffImplyImply'.mp;
      apply deduct;

      have d₁ : [(~~p ⟶ ~~q) ⋏ ~(p ⟶ q)] ⊢[𝓢] ~~p ⟶ ~~q := conj₁' (q := ~(p ⟶ q)) $ FiniteContext.byAxm (by simp);
      have d₂ : [(~~p ⟶ ~~q) ⋏ ~(p ⟶ q)] ⊢[𝓢] ~~p ⋏ ~q := demorgan₃' $ (contra₀' implyOfNotOr) ⨀ (conj₂' (p := (~~p ⟶ ~~q)) $ FiniteContext.byAxm (by simp))
      exact conj₃' (conj₂' d₂) (d₁ ⨀ (conj₁' d₂))
    )
    (introFalsumOfAnd (p := ~q));

@[simp] lemma dn_collect_imply! [HasEFQ 𝓢] : 𝓢 ⊢! (~~p ⟶ ~~q) ⟶ ~~(p ⟶ q) := ⟨dnCollectImply⟩

def dnCollectImply' [HasEFQ 𝓢] (b : 𝓢 ⊢ ~~p ⟶ ~~q) : 𝓢 ⊢ ~~(p ⟶ q) := dnCollectImply ⨀ b
@[simp] lemma dn_collect_imply'! [HasEFQ 𝓢] (b : 𝓢 ⊢! ~~p ⟶ ~~q) : 𝓢 ⊢! ~~(p ⟶ q) := ⟨dnCollectImply' b.some⟩


def andImplyAndOfImply {p q p' q' : F} (bp : 𝓢 ⊢ p ⟶ p') (bq : 𝓢 ⊢ q ⟶ q') : 𝓢 ⊢ p ⋏ q ⟶ p' ⋏ q' :=
  deduct' <| andIntro
    (deductInv' <| impTrans conj₁ bp)
    (deductInv' <| impTrans conj₂ bq)

def andIffAndOfIff {p q p' q' : F} (bp : 𝓢 ⊢ p ⟷ p') (bq : 𝓢 ⊢ q ⟷ q') : 𝓢 ⊢ p ⋏ q ⟷ p' ⋏ q' :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp) (andRight bq))

def conj'IffConj : (Γ : List F) → 𝓢 ⊢ Γ.conj' ⟷ Γ.conj
  | []          => iffId ⊤
  | [p]         => iffIntro (deduct' <| andIntro (FiniteContext.byAxm (by simp)) verum) conj₁
  | p :: q :: Γ => andIffAndOfIff (iffId p) (conj'IffConj (q :: Γ))
@[simp] lemma conj'IffConj! : 𝓢 ⊢! Γ.conj' ⟷ Γ.conj := ⟨conj'IffConj Γ⟩


lemma implyLeft_conj_eq_conj'! : 𝓢 ⊢! Γ.conj ⟶ p ↔ 𝓢 ⊢! Γ.conj' ⟶ p := implyLeftReplaceIff'! $ iffComm'! conj'IffConj!


lemma generalConj'! (h : p ∈ Γ) : 𝓢 ⊢! Γ.conj' ⟶ p := implyLeftReplaceIff'! conj'IffConj! |>.mpr (generalConj! h)


namespace FiniteContext

def ofDef' {Γ : List F} {p : F} (b : 𝓢 ⊢ Γ.conj' ⟶ p) : Γ ⊢[𝓢] p := ofDef <| impTrans (andRight <| conj'IffConj Γ) b
def ofDef'! (b : 𝓢 ⊢! Γ.conj' ⟶ p) : Γ ⊢[𝓢]! p := ⟨ofDef' b.some⟩

def toDef' {Γ : List F} {p : F} (b : Γ ⊢[𝓢] p) : 𝓢 ⊢ Γ.conj' ⟶ p := impTrans (andLeft <| conj'IffConj Γ) (toDef b)
def toDef'! (b : Γ ⊢[𝓢]! p) : 𝓢 ⊢! Γ.conj' ⟶ p := ⟨toDef' b.some⟩

lemma provable_iff' {p : F} : Γ ⊢[𝓢]! p ↔ 𝓢 ⊢! Γ.conj' ⟶ p := ⟨fun h ↦ ⟨toDef' h.get⟩, fun h ↦ ⟨ofDef' h.get⟩⟩

end FiniteContext



lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! Γ.conj') ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons p Γ hΓ ih =>
    simp_all;
    constructor;
    . intro h;
      constructor;
      . exact conj₁'! h;
      . exact ih.mp (conj₂'! h);
    . rintro ⟨h₁, h₂⟩;
      exact conj₃'! h₁ (ih.mpr h₂);


def implyOrLeft' (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ (r ⋎ q) := by
  apply deduct';
  apply disj₁';
  apply deductInv;
  exact of h;

lemma implyOrLeft'! (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ (r ⋎ q) := ⟨implyOrLeft' h.some⟩

def implyOrRight' (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ q ⟶ (p ⋎ r) := by
  apply deduct';
  apply disj₂';
  apply deductInv;
  exact of h;

lemma implyOrRight'! (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! q ⟶ (p ⋎ r) := ⟨implyOrRight' h.some⟩

lemma or_assoc'! : 𝓢 ⊢! p ⋎ (q ⋎ r) ↔ 𝓢 ⊢! (p ⋎ q) ⋎ r := by
  constructor;
  . intro h;
    exact disj₃'!
      (by apply implyOrLeft'!; apply implyOrLeft'!; simp;)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have : [q ⋎ r] ⊢[𝓢]! q ⋎ r := by_axm! (by simp);
        exact disj₃'! (by apply implyOrLeft'!; apply implyOrRight'!; simp) (by apply implyOrRight'!; simp) this;
      )
      h;
  . intro h;
    exact disj₃'!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have : [p ⋎ q] ⊢[𝓢]! p ⋎ q := by_axm! (by simp);
        exact disj₃'! (by apply implyOrLeft'!; simp) (by apply implyOrRight'!; apply implyOrLeft'!; simp) this;
      )
      (by apply implyOrRight'!; apply implyOrRight'!; simp;)
      h;

lemma and_assoc! : 𝓢 ⊢! (p ⋏ q) ⋏ r ⟷ p ⋏ (q ⋏ r) := by
  apply iff_intro!;
  . apply FiniteContext.deduct'!;
    have hpqr : [(p ⋏ q) ⋏ r] ⊢[𝓢]! (p ⋏ q) ⋏ r := FiniteContext.by_axm! (by simp);
    have hp : [(p ⋏ q) ⋏ r] ⊢[𝓢]! p := conj₁'! $ conj₁'! hpqr;
    have hq : [(p ⋏ q) ⋏ r] ⊢[𝓢]! q := conj₂'! $ conj₁'! hpqr;
    have hr : [(p ⋏ q) ⋏ r] ⊢[𝓢]! r := conj₂'! hpqr;
    exact conj₃'! hp (conj₃'! hq hr);
  . apply FiniteContext.deduct'!;
    have hpqr : [p ⋏ (q ⋏ r)] ⊢[𝓢]! p ⋏ q ⋏ r := FiniteContext.by_axm! (by simp);
    have hp : [p ⋏ (q ⋏ r)] ⊢[𝓢]! p := conj₁'! hpqr;
    have hq : [p ⋏ (q ⋏ r)] ⊢[𝓢]! q := conj₁'! $ conj₂'! hpqr;
    have hr : [p ⋏ (q ⋏ r)] ⊢[𝓢]! r := conj₂'! $ conj₂'! hpqr;
    apply conj₃'!;
    . exact conj₃'! hp hq;
    . exact hr;

lemma id_conj'! (he : ∀ g ∈ Γ, g = p) : 𝓢 ⊢! p ⟶ Γ.conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp_all only [List.conj'_nil, IsEmpty.forall_iff, forall_const]; exact dhyp! $ verum!;
  | hsingle => simp_all only [List.mem_singleton, forall_eq, List.conj'_singleton, imp_id!];
  | hcons r Γ h ih =>
    simp [List.conj'_cons_nonempty h];
    simp at he;
    have ⟨he₁, he₂⟩ := he;
    subst he₁;
    exact implyRightAnd! imp_id! (ih he₂);

lemma replace_imply_left_conj'! (he : ∀ g ∈ Γ, g = p) (hd : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! p ⟶ q := imp_trans! (id_conj'! he) hd

lemma implyLeft_cons_conj'! : 𝓢 ⊢! (p :: Γ).conj' ⟶ q ↔ 𝓢 ⊢! p ⋏ Γ.conj' ⟶ q := by
  induction Γ with
  | nil =>
    simp [andImplyIffImplyImply'!];
    constructor;
    . intro h; apply imp_swap'!; exact dhyp! h;
    . intro h; exact imp_swap'! h ⨀ verum!;
  | cons q ih => simp;

lemma imply_left_concat_conj'! : 𝓢 ⊢! (Γ ++ Δ).conj' ⟶ Γ.conj' ⋏ Δ.conj' := by
  apply FiniteContext.deduct'!;
  have : [(Γ ++ Δ).conj'] ⊢[𝓢]! (Γ ++ Δ).conj' := FiniteContext.by_axm! (by simp);
  have d := iff_provable_list_conj.mp this;
  apply conj₃'!;
  . apply iff_provable_list_conj.mpr;
    intro p hp;
    exact d p (by simp; left; exact hp);
  . apply iff_provable_list_conj.mpr;
    intro p hp;
    exact d p (by simp; right; exact hp);

@[simp]
lemma forthbackConjRemove : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ Γ.conj' := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have d : [(Γ.remove p).conj' ⋏ p] ⊢[𝓢]! (Γ.remove p).conj' ⋏ p := by_axm! (by simp);
  apply iff_provable_list_conj.mpr;
  intro q hq;
  by_cases e : q = p;
  . subst e; exact conj₂'! d;
  . exact iff_provable_list_conj.mp (conj₁'! d) q (by apply List.mem_remove_iff.mpr; simp_all);

lemma implyLeftRemoveConj' (b : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ q := imp_trans! (by simp) b

lemma disj_allsame! [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) : 𝓢 ⊢! Γ.disj' ⟶ p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp_all [List.disj'_nil, efq!];
  | hsingle => simp_all [List.mem_singleton, List.disj'_singleton, imp_id!];
  | hcons q Δ hΔ ih =>
    simp [List.disj'_cons_nonempty hΔ];
    simp at hd;
    have ⟨hd₁, hd₂⟩ := hd;
    subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact disj₃'!
      (by simp)
      (weakening! (by simp) $ provable_iff_provable.mp $ ih hd₂)
      (show [q ⋎ List.disj' Δ] ⊢[𝓢]! q ⋎ List.disj' Δ by exact by_axm! (by simp));

lemma disj_allsame'! [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) (h : 𝓢 ⊢! Γ.disj') : 𝓢 ⊢! p := (disj_allsame! hd) ⨀ h


instance [HasDNE 𝓢] : HasEFQ 𝓢 where
  efq p := by
    apply contra₃';
    simp [NegDefinition.neg];
    exact impSwap' imply₁;


def dneOr [HasDNE 𝓢] (d : 𝓢 ⊢ ~~p ⋎ ~~q) : 𝓢 ⊢ p ⋎ q := disj₃' (impTrans dne disj₁) (impTrans dne disj₂) d

instance [HasDNE 𝓢] : HasLEM 𝓢 where
  lem _ := dneOr $ NotOrOfImply' dni

/-
instance [HasLEM 𝓢] [HasEFQ 𝓢] : HasDNE 𝓢 where
  dne p := by sorry;
-/

end LO.System
