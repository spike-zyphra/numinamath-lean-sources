import Mathlib

theorem number_theory_610024 (A B : ℕ) (Ane0 : A ≠ 0) (Bne0 : B ≠ 0)
(digA : A < 10) (digB : B < 10) : A * Nat.ofDigits 10 [B, A] + B = Nat.ofDigits 10 [B, B] ↔
(A, B) = (2, 5) := by
  simp [Nat.ofDigits, Finset.sum] at *
  constructor
  · -- Forward direction: If $A \cdot \overline{AB}+B=\overline{B B}$ then $(A, B) = (2,5)$
    intro h
    have h1 : A ≤ 9 := by linarith
    have h2 : B ≤ 9 := by linarith
    interval_cases A <;> interval_cases B <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction: If $(A, B) = (2,5)$ then $A \cdot \overline{AB}+B=\overline{B B}$
    rintro ⟨rfl, rfl⟩
    all_goals norm_num