import Logic.Modal.Normal.Formula

namespace LO.Modal.Normal

variable (α : Type u) (β : Type v)

def Frame := (Formula β) → α → α → Prop

def Valuation := α → β → Prop

structure Model where
  frame : Frame α β
  val : Valuation α β

namespace Formula

variable {α β}

def Satisfies (M : Model α β) (w : α) : Formula β → Prop
  | atom a => M.val w a
  | falsum  => False
  | and p q => (Satisfies M w p) ∧ (Satisfies M w q)
  | or p q  => (Satisfies M w p) ∨ (Satisfies M w q)
  | imp p q => ¬(Satisfies M w p) ∨ (Satisfies M w q)
  | box p   => ∀ w', M.frame p w w' → Satisfies M w' p

notation w " ⊩[" M "] " p => Satisfies M w p

namespace Satisfies

variable {M : Model α β}

@[simp] lemma atom_def : (w ⊩[M] atom a) ↔ (M.val w a) := by simp [Satisfies];
@[simp] lemma falsum_def : ¬(w ⊩[M] ⊥) := by simp [Satisfies];
@[simp] lemma and_def : (w ⊩[M] p ⋏ q) ↔ (w ⊩[M] p) ∧ (w ⊩[M] q) := by simp [Satisfies];
@[simp] lemma or_def : (w ⊩[M] p ⋎ q) ↔ (w ⊩[M] p) ∨ (w ⊩[M] q) := by simp [Satisfies];

lemma imp_def : (w ⊩[M] p ⟶ q) ↔ (¬(w ⊩[M] p)) ∨ (w ⊩[M] q) := by simp [Satisfies];
@[simp] lemma imp_def' : (w ⊩[M] p ⟶ q) ↔ (w ⊩[M] p) → (w ⊩[M] q) := by simp [Satisfies, imp_iff_not_or];

@[simp] lemma box_def : (w ⊩[M] □p) ↔ (∀ w', M.frame p w w' → (w' ⊩[M] p)) := by simp [Satisfies]

@[simp] lemma neg_def : (w ⊩[M] ~p) ↔ ¬(w ⊩[M] p) := by simp [Satisfies]

end Satisfies

def Models (M : Model α β) (p : Formula β) : Prop := ∀ w, w ⊩[M] p
notation "⊧[" M "] " p => Models M p

namespace Models

variable {M : Model α β} [Inhabited α]

@[simp] lemma neg_def : (⊧[M] ~p) → ¬(⊧[M] p) := by simp_all [Models, Satisfies.neg_def];
@[simp] lemma falsum_def : ¬(⊧[M] ⊥) := by simp [Models, Satisfies.falsum_def];

lemma modus_ponens (h₁ : ⊧[M] p ⟶ q) (h₂ : ⊧[M] p) : ⊧[M] q := by simp [Models, Satisfies.imp_def] at *; tauto
lemma necessitation (h : ⊧[M] p) : ⊧[M] □p := by simp [Models, Satisfies.box_def] at *; tauto

end Models

def Frames (F : Frame α β) (p : Formula β) : Prop := ∀ V, ⊧[⟨F, V⟩] p
notation "⊧[" F "] " p => Frames F p

namespace Frames

variable {F : Frame α β}

lemma modus_ponens (h₁ : ⊧[F] p ⟶ q) (h₂ : ⊧[F] p) : ⊧[F] q := by intro V; exact Models.modus_ponens (h₁ V) (h₂ V)
lemma necessitation (h : ⊧[F] p) : ⊧[F] □p := by intro V; exact Models.necessitation (h V)

end Frames

end Formula

def Theory.Satisfies (M : Model α β) (w : α) (Γ : Theory β) : Prop := ∀ p ∈ Γ, w ⊩[M] p
notation w " ⊩[" M "] " Γ => Theory.Satisfies M w Γ

def Theory.Models (M : Model α β) (Γ : Theory β) : Prop := ∀ p ∈ Γ, ⊧[M] p
notation "⊧[" M "] " Γ => Theory.Models M Γ

def Theory.Frames (F : Frame α β) (Γ : Theory β) : Prop := ∀ p ∈ Γ, ⊧[F] p
notation "⊧[" F "] " Γ => Theory.Frames F Γ

end LO.Modal.Normal
