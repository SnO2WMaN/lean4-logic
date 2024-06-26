import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.HilbertStyle

namespace LO.Modal.Standard

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | p ⋏ q => (BoxdotTranslation p) ⋏ (BoxdotTranslation q)
  | p ⋎ q => (BoxdotTranslation p) ⋎ (BoxdotTranslation q)
  | box p => ⊡(BoxdotTranslation p)
postfix:75 "ᵇ" => Formula.BoxdotTranslation

open System
open Formula
open StandardModalLogicalConnective (boxdot)

variable {p : Formula α}

lemma boxdotTranslatedK4_of_S4 (h : 𝐒𝟒 ⊢! p) : 𝐊𝟒 ⊢! pᵇ := by
  induction h.some using Deduction.inducition_with_nec with
  | hMaxm a =>
    rcases a with (hK | hT) | hFour;
    . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp [Axioms.K, BoxdotTranslation]; apply boxdot_axiomK!;
    . obtain ⟨_, e⟩ := hT; subst_vars; dsimp [Axioms.T, BoxdotTranslation]; apply boxdot_axiomT!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; dsimp [Axioms.Four, BoxdotTranslation]; apply boxdot_axiomFour!;
  | hNec hp ihp =>
    dsimp [BoxdotTranslation];
    exact boxdot_nec! $ ihp ⟨hp⟩;
  | hMdp hpq hp ihpq ihp =>
    dsimp [BoxdotTranslation] at ihpq ihp;
    exact (ihpq ⟨hpq⟩) ⨀ (ihp ⟨hp⟩);
  | _ =>
    dsimp [BoxdotTranslation];
    try first
    | apply verum!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply imply₁!;
    | apply imply₂!;
    | apply dne!;

lemma iff_boxdotTranslation_S4 : 𝐒𝟒 ⊢! p ⟷ pᵇ := by
  induction p using Formula.rec' with
  | hand p q ihp ihq => dsimp [BoxdotTranslation]; exact and_replace_iff! ihp ihq;
  | hor p q ihp ihq => dsimp [BoxdotTranslation]; exact or_replace_iff! ihp ihq;
  | himp p q ihp ihq => dsimp [BoxdotTranslation]; exact imp_replace_iff! ihp ihq;
  | hbox p ihp =>
    dsimp [BoxdotTranslation];
    exact iff_trans! (box_iff! ihp) iff_box_boxdot!;
  | _ => dsimp [BoxdotTranslation]; exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : 𝐊𝟒 ⊢! pᵇ) : 𝐒𝟒 ⊢! p := by
  exact (conj₂'! iff_boxdotTranslation_S4) ⨀ (reducible_iff.mp $ reducible_K4_S4) h

theorem iff_S4_boxdotTranslatedK4 : 𝐒𝟒 ⊢! p ↔ 𝐊𝟒 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;

end LO.Modal.Standard
