import Logic.Propositional.Superintuitionistic.Intuitionistic.Kripke.Completeness

namespace LO.Propositional.Superintuitionistic

open Formula Theory
open Hilbert
open Set

variable [Encodable β] [DecidableEq β]

namespace Intuitionistic.Kripke

open Kripke

private def DPCounterModel (M₁ : Kripke.Model γ₁ β) (M₂ : Kripke.Model γ₂ β) (w₁ : γ₁) (w₂ : γ₂) : Kripke.Model (Unit ⊕ γ₁ ⊕ γ₂) β where
  frame w v :=
    match w, v with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl v) => M₁.frame w₁ v
    | (Sum.inl _), (Sum.inr $ Sum.inr v) => M₂.frame w₂ v
    | (Sum.inr $ Sum.inl w), (Sum.inr $ Sum.inl v) => M₁.frame w v
    | (Sum.inr $ Sum.inr w), (Sum.inr $ Sum.inr v) => M₂.frame w v
    | _, _ => False
  val w a :=
    match w with
    | Sum.inr $ Sum.inl w => M₁.val w a
    | Sum.inr $ Sum.inr w => M₂.val w a
    | _ => False
  refl := by
    simp only [Reflexive, Sum.forall, forall_const, true_and];
    constructor <;> { intros; rfl };
  trans := by
    simp only [Transitive, Sum.forall, forall_true_left, imp_self, forall_const, true_and, IsEmpty.forall_iff, implies_true, and_true, and_self, imp_false];
    constructor;
    . constructor;
      . intros; apply M₁.trans (by assumption) (by assumption);
      . intros; apply M₂.trans (by assumption) (by assumption);
    . constructor;
      . intros; apply M₁.trans (by assumption) (by assumption);
      . intros; apply M₂.trans (by assumption) (by assumption);
  hereditary := by
    simp only [Sum.forall, imp_false, not_false_eq_true, implies_true, forall_true_left, forall_const, IsEmpty.forall_iff, and_self, true_and, and_true];
    constructor;
    . intro _ _; apply M₁.hereditary;
    . intro _ _; apply M₂.hereditary;

variable {M₁ : Kripke.Model γ₁ β} {M₂ : Kripke.Model γ₂ β}

private lemma DPCounterModel_left {p : Formula β} : (w ⊩ⁱ[M₁] p) ↔ (Sum.inr $ Sum.inl w) ⊩ⁱ[DPCounterModel M₁ M₂ w₁ w₂] p := by
  induction p using rec' generalizing w with
  | himp p₁ p₂ ih₁ ih₂ =>
    constructor;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₁.frame w v' ∧ v = (Sum.inr (Sum.inl v')) := by
        simp [DPCounterModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      have := ih₁.mpr hp₁;
      have := h v hv this;
      have := ih₂.mp this;
      simpa;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      have := ih₁.mp hp₁;
      have := h (Sum.inr $ Sum.inl v) (by simpa [DPCounterModel]) this;
      have := ih₂.mpr this;
      simpa;
  | _ => simp_all [DPCounterModel];

private lemma DPCounterModel_right {p : Formula β} : (w ⊩ⁱ[M₂] p) ↔ (Sum.inr $ Sum.inr w) ⊩ⁱ[DPCounterModel M₁ M₂ w₁ w₂] p := by
  induction p using rec' generalizing w with
  | himp p₁ p₂ ih₁ ih₂ =>
    constructor;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₂;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₂.frame w v' ∧ v = (Sum.inr (Sum.inr v')) := by
        simp [DPCounterModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      have := ih₁.mpr hp₂;
      have := h v hv this;
      have := ih₂.mp this;
      simpa;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      have := ih₁.mp hp₁;
      have := h (Sum.inr $ Sum.inr v) (by simpa [DPCounterModel]) this;
      have := ih₂.mpr this;
      simpa;
  | _ => simp_all [DPCounterModel];

theorem disjunctive {p q : Formula β} : ∅ ⊢ⁱ! p ⋎ q → ∅ ⊢ⁱ! p ∨ ∅ ⊢ⁱ! q := by
  contrapose;
  intro h;
  apply not_imp_not.mpr Kripke.sounds;

  have ⟨(hp : ∅ ⊬ⁱ! p), (hq : ∅ ⊬ⁱ! q)⟩ := not_or.mp h;
  obtain ⟨γ₁, M₁, w₁, hp⟩ := by simpa [Formula.Intuitionistic.Kripke.Consequence] using not_imp_not.mpr Kripke.completes hp;
  obtain ⟨γ₂, M₂, w₂, hq⟩ := by simpa [Formula.Intuitionistic.Kripke.Consequence] using not_imp_not.mpr Kripke.completes hq;
  let M : Kripke.Model (Unit ⊕ γ₁ ⊕ γ₂) β := DPCounterModel M₁ M₂ w₁ w₂;

  simp [Formula.Intuitionistic.Kripke.Consequence, Theory.Intuitionistic.Kripke.Satisfies];
  existsi _, M, Sum.inl ();

  have : ¬Sum.inl () ⊩ⁱ[M] p := not_imp_not.mpr (Kripke.hereditary_formula (by simp [M]; rfl)) (DPCounterModel_left.not.mp hp)
  have : ¬Sum.inl () ⊩ⁱ[M] q := not_imp_not.mpr (Kripke.hereditary_formula (by simp [M]; rfl)) (DPCounterModel_right.not.mp hq)

  simp_all;

end Intuitionistic.Kripke

def Formula.harrop : Formula α → Prop
| atom _ => True
| ⊤      => True
| ⊥      => True
| p ⋏ q  => p.harrop ∧ q.harrop
| _ ⟶ q  => q.harrop
| _      => False

namespace Formula

@[simp] lemma harrop_and {p q : Formula α} : p.harrop ∧ q.harrop → (p ⋏ q).harrop := by simp [Formula.harrop];
@[simp] lemma harrop_imp {p q : Formula α} : q.harrop → (p ⟶ q).harrop := by simp [Formula.harrop];
@[simp] lemma harrop_neg {p : Formula α} : (~p).harrop := by simp [Formula.harrop];
@[simp] lemma harrop_verum : (⊤ : Formula α).harrop := by simp [Formula.harrop];
@[simp] lemma harrop_valsum : (⊥ : Formula α).harrop := by simp [Formula.harrop];
@[simp] lemma not_harrop_or {p q : Formula α} : ¬(p ⋎ q).harrop := by simp [Formula.harrop];

end Formula

@[simp] def Theory.harrop (T : Theory β) := ∀ p ∈ T, p.harrop

theorem Intuitionistic.Kripke.harrop_disjunctive {T : Theory β} (hT : T.harrop) : T ⊢ⁱ! p ⋎ q → T ⊢ⁱ! p ∨ T ⊢ⁱ! q := by
  generalize e : p ⋎ q = x
  intro d;
  induction d.some with
  | axm h =>
    subst e;
    have : (p ⋎ q).harrop := by apply hT; simpa;
    contradiction;
  | @modusPonens r _ hpq hr ihrpq ihr => sorry;
  | _ => sorry

end LO.Propositional.Superintuitionistic
