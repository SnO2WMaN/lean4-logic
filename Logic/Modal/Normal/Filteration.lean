import Mathlib.Tactic.Linarith
import Logic.Modal.Normal.Completeness

namespace LO.Modal.Normal

open Formula Theory

section

variable {α : Type} [DecidableEq α]
variable {p q : Formula α}

namespace Formula

def length : Formula α → ℕ
  | atom _  => 1
  | ⊥       => 1
  | p ⟶ q  => p.length + q.length + 1
  | p ⋏ q   => p.length + q.length + 1
  | p ⋎ q   => p.length + q.length + 1
  | box p   => p.length + 1

def subformulae : Formula α → Finset (Formula α)
  | ⊥       => {⊥}
  | atom a  => {atom a}
  | p ⟶ q  => {p ⟶ q} ∪ p.subformulae ∪ q.subformulae
  | p ⋏ q   => {p ⋏ q} ∪ p.subformulae ∪ q.subformulae
  | p ⋎ q   => {p ⋎ q} ∪ p.subformulae ∪ q.subformulae
  | box p   => {□p} ∪ p.subformulae

@[simp] lemma subformulae_atom : (atom p).subformulae = {atom p} := by simp [subformulae]
@[simp] lemma subformulae_atom_card : (atom p).subformulae.card = 1 := by simp [subformulae]

@[simp] lemma subformulae_bot : (⊥ : Formula α).subformulae = {⊥} := by simp [subformulae]
@[simp] lemma subformulae_bot_card : (⊥ : Formula α).subformulae.card = 1 := by simp [subformulae]

@[simp] lemma subformulae_or : (p ⋎ q).subformulae = {p ⋎ q} ∪ p.subformulae ∪ q.subformulae := by simp [subformulae]

@[simp] lemma subformulae_and : (p ⋏ q).subformulae = {p ⋏ q} ∪ p.subformulae ∪ q.subformulae := by simp [subformulae]

@[simp] lemma subformulae_imp : (p ⟶ q).subformulae = {p ⟶ q} ∪ p.subformulae ∪ q.subformulae := by simp [subformulae]

@[simp] lemma subformulae_box : (□p).subformulae = {□p} ∪ p.subformulae := by simp [Formula.subformulae]

lemma subformulae_self (p : Formula α) : p ∈ p.subformulae := by induction p using rec' <;> simp_all [subformulae]

lemma subformulae_imp_include₁ : p ∈ (p ⟶ q).subformulae := by simp [subformulae, subformulae_self];
lemma subformulae_imp_include₂ : q ∈ (p ⟶ q).subformulae := by simp [subformulae, subformulae_self];

lemma subformulae_card_max (p : Formula α) : p.subformulae.card ≤ p.length := by
  induction p using rec' <;> simp_all [subformulae, length];
  case hbox p ihp =>
    have : ({(□p)} : Context α).card = 1 := by simp;
    have := Finset.card_union_le ({□p}) (p.subformulae);
    linarith;
  case himp p q ihp ihq =>
    have : ({(p ⟶ q)} : Context α).card = 1 := by simp;
    have := Finset.card_union_le (p.subformulae) (q.subformulae);
    have := Finset.card_union_le {(p ⟶ q)} ((p.subformulae) ∪ (q.subformulae))
    linarith;
  case hor p q ihp ihq =>
    have : ({(p ⋎ q)} : Context α).card = 1 := by simp;
    have := Finset.card_union_le (p.subformulae) (q.subformulae);
    have := Finset.card_union_le {(p ⋎ q)} ((p.subformulae) ∪ (q.subformulae))
    linarith;
  case hand p q ihp ihq =>
    have : ({(p ⋏ q)} : Context α).card = 1 := by simp;
    have := Finset.card_union_le (p.subformulae) (q.subformulae);
    have := Finset.card_union_le {(p ⋏ q)} ((p.subformulae) ∪ (q.subformulae))
    linarith;

end Formula

namespace Theory

def atoms (Γ : Theory α) : Set α := { a | atom a ∈ Γ }

lemma atoms_iff {Γ : Theory α} {a : α} : a ∈ Γ.atoms ↔ atom a ∈ Γ := by simp [atoms]

def subformulae (Γ : Theory α) : Set (Formula α) := ⋃ p ∈ Γ, p.subformulae

class SubformulaeClosed (Γ : Theory α) where
  closed : ∀ {p}, p ∈ Γ → ↑p.subformulae ⊆ Γ

end Theory

section

variable {Γ : Theory α} [SubformulaeClosed Γ] {p q : Formula α}

lemma subformulae_closed_imp (h : p ⟶ q ∈ Γ) : p ∈ Γ ∧ q ∈ Γ := by
  have := SubformulaeClosed.closed h;
  simp [Formula.subformulae] at this;
  constructor;
  . apply this.2.1; exact subformulae_self p;
  . apply this.2.2; exact subformulae_self q;

lemma subformulae_closed_and (h : p ⋏ q ∈ Γ) : p ∈ Γ ∧ q ∈ Γ := by
  have := SubformulaeClosed.closed h;
  simp [Formula.subformulae] at this;
  constructor;
  . apply this.2.1; exact subformulae_self p;
  . apply this.2.2; exact subformulae_self q;

lemma subformulae_closed_or (h : p ⋎ q ∈ Γ) : p ∈ Γ ∧ q ∈ Γ := by
  have := SubformulaeClosed.closed h;
  simp [Formula.subformulae] at this;
  constructor;
  . apply this.2.1; exact subformulae_self p;
  . apply this.2.2; exact subformulae_self q;

lemma subformulae_closed_box (h : □p ∈ Γ) : p ∈ Γ := by
  have := SubformulaeClosed.closed h;
  simp [Formula.subformulae] at this;
  apply this.2; exact subformulae_self p;

end

end

variable {α β : Type} [DecidableEq β]
variable (M : Model α β) (Γ : Theory β) [SubformulaeClosed Γ]

def FilterEquiv (w₁ w₂ : α) := ∀ p ∈ Γ, (⊧ᴹ[M, w₁] p) ↔ (⊧ᴹ[M, w₂] p)

local infix:50 "≈ᶠ"  => FilterEquiv M Γ

@[refl]
lemma FilterEquiv.refl : w ≈ᶠ w := by simp [FilterEquiv]

@[symm]
lemma FilterEquiv.symm : (w₁ ≈ᶠ w₂) → (w₂ ≈ᶠ w₁) := by simp_all [FilterEquiv]

@[trans]
lemma FilterEquiv.trans : (w₁ ≈ᶠ w₂) → (w₂ ≈ᶠ w₃) → (w₁ ≈ᶠ w₃) := by simp_all [FilterEquiv]

@[instance]
lemma FilterEquiv.equiv : Equivalence (· ≈ᶠ ·) := ⟨
  by apply FilterEquiv.refl,
  by apply FilterEquiv.symm,
  by apply FilterEquiv.trans,
⟩

instance FilterEquiv.isSetoid : Setoid α := ⟨(· ≈ᶠ ·), equiv M Γ⟩

structure FilteredModel extends Model (Quotient (FilterEquiv.isSetoid M Γ)) β where
  frame_cond₁ : ∀ w v, M.frame w v → frame ⟦w⟧ ⟦v⟧
  frame_cond₂ : ∀ w v, frame ⟦w⟧ ⟦v⟧ → (∀ p ∈ □⁻¹Γ, (⊧ᴹ[M, w] □p) → (⊧ᴹ[M, v] p))
  val_cond : ∀ a ∈ Γ.atoms, ∀ w, M.val w a ↔ val ⟦w⟧ a

lemma filtered_lemma (FM : FilteredModel M Γ) : ∀ p ∈ Γ, ∀ w, (⊧ᴹ[M, w] p) ↔ (⊧ᴹ[FM.toModel, ⟦w⟧] p) := by
  intro p hp;
  induction p using rec' <;> try { intros; simp; }
  case hatom a =>
    intro w;
    constructor;
    . apply FM.val_cond a hp w |>.mp;
    . apply FM.val_cond a hp w |>.mpr;
  case himp q₁ q₂ ih₁ ih₂ =>
    have ⟨hq₁, hq₂⟩ := subformulae_closed_imp hp;
    have := ih₁ hq₁;
    have := ih₂ hq₂;
    simp_all;
  case hor q₁ q₂ ih₁ ih₂ =>
    have ⟨hq₁, hq₂⟩ := subformulae_closed_or hp;
    have := ih₁ hq₁;
    have := ih₂ hq₂;
    simp_all;
  case hand q₁ q₂ ih₁ ih₂ =>
    have ⟨hq₁, hq₂⟩ := subformulae_closed_and hp;
    have := ih₁ hq₁;
    have := ih₂ hq₂;
    simp_all;
  case hbox q ih =>
    intro w;
    have hq := subformulae_closed_box hp;
    constructor;
    . intro hbq Qv hQv;
      have ⟨v, hv⟩ := Qv.exists_rep;
      rw [←hv];
      rw [←hv] at hQv;
      have h₁ := FM.frame_cond₂ w v hQv q (by simpa [prebox]) hbq;
      exact ih hq _ |>.mp $ h₁;
    . intro hbq v hwv;
      simp at hbq;
      have h₁ := hbq ⟦v⟧ $ FM.frame_cond₁ w v hwv;
      exact ih hq v |>.mpr h₁;

def FinestFilteredModal : FilteredModel M Γ where
  val Qw a := M.val Qw.out' a
  val_cond := by
    simp;
    intro a ha w;
    constructor;
    . intro h;
      have : ⊧ᴹ[M, w] (atom a) := h;
      have := atoms_iff.mp ha;
      sorry;
    . sorry;
  frame Qw Qv := ∃ w v, Qw = ⟦w⟧ ∧ Qv = ⟦v⟧ ∧ M.frame w v
  frame_cond₁ := by
    simp;
    intro w₁ w₂ h;
    existsi w₁, rfl, w₂, rfl;
    trivial;
  frame_cond₂ := by
    simp;
    intro w₁ w₂ v₁ hw₁v₁ v₂ hw₂v₂ hv₁v₂ p hp h;
    apply h w₂;
    sorry;

def CoarsestFilteredModal : FilteredModel M Γ where
  frame Qw Qv := ∀ p ∈ □⁻¹Γ, (⊧ᴹ[M, Qw.out] □p) ↔ (⊧ᴹ[M, Qv.out] p)
  frame_cond₁ := by
    simp;
    intro w₁ w₂ h p hp;
    constructor;
    . intro hf; have := hf w₂;
    . intros; sorry;
  frame_cond₂ := by
    simp;
    sorry;

end LO.Modal.Normal
