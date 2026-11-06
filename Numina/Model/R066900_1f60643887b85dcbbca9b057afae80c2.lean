import Mathlib

theorem number_theory_4305 (A B : ℕ) (h₀ : 0 ≤ A ∧ A ≤ 9) (h₁ : 0 ≤ B ∧ B ≤ 9)
    (h₂ : 455 ∣ (1820000 + 1000 * A + 100 * B + 25)) :
    1820000 + 1000 * A + 100 * B + 25 = 1826825 := by 
  have hA1 : 0 ≤ A := h₀.left
  have hA2 : A ≤ 9 := h₀.right
  have hB1 : 0 ≤ B := h₁.left
  have hB2 : B ≤ 9 := h₁.right
  interval_cases A <;> interval_cases B <;> omega