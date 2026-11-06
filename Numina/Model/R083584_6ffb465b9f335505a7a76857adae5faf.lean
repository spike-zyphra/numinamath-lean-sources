import Mathlib

theorem number_theory_187200 (a b : ℕ) (ha : ¬ 10 ∣ a) (hb : ¬ 10 ∣ b)
    (h : a * b = 1000) : a + b = 133 := by
  have h2 : a ≤ 1000 := by 
    by_cases h1 : a ≤ 1000
    · exact h1
    · -- Assume a > 1000 and derive contradiction
      push_neg at h1
      have h1 : a > 1000 := by linarith
      have h3 : b = 0 := by
        nlinarith
      rw [h3] at h
      nlinarith
  interval_cases a <;> omega