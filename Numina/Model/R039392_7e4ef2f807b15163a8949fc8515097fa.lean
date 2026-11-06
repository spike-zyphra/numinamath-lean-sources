import Mathlib

theorem number_theory_170113 (a b c : ℕ) (h₀ : a < b) (h₁ : b < c)
    (h₂ : a * b * c = 270) (h₃ : 4 * (a + b + c) = 80) :
    a = 5 ∧ b = 6 ∧ c = 9 := by
  -- From 4 \cdot (a + b + c) = 80 \implies a + b + c = 20
  have h4 : a + b + c = 20 := by
    omega
  -- Now we have c = 20 - a - b.
  have h5 : c = 20 - a - b := by
    omega
  -- Substitute c in the product equation
  rw [h5] at h₂
  -- Derive upper bound for a
  have h6 : a ≤ 6 := by
    nlinarith [h₀, h₁, h4]
  -- Derive upper bound for b
  have h7 : b ≤ 9 := by
    nlinarith [h₀, h₁, h4]
  -- Use exhaustive search
  interval_cases a <;> interval_cases b
    <;> omega