import Mathlib

theorem algebra_322473 (m : ℤ) (h : ∃! x : ℕ, x > 0 ∧ 6 * x ^ 2 + 2 * (m - 13) * x + 12 - m = 0) :
    m = 8 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have h_eq : (x : ℤ) > 0 := by
    omega
  have heq : 6 * x ^ 2 + 2 * (m - 13) * x + 12 - m = 0 := by
    tauto
  have heq3 : (x : ℤ) = 1 := by
    by_cases h' : (x : ℤ) > 1
    · -- Assume x > 1. Need to derive contradiction.
      have h10 : (2 * (x : ℤ) - 1) ∣ (x - 1 : ℤ) := by
        have h3 : (2 * (x : ℤ) - 1) ∣ (-6 * x ^ 2 + 26 * x - 12 : ℤ) := by
          have heq2 : (2 * (x : ℤ) - 1) * m = -6 * x ^ 2 + 26 * x - 12 := by
            nlinarith
          have h_eq3 : (2 * (x : ℤ) - 1) ∣ (-6 * x ^ 2 + 26 * x - 12 : ℤ) := by
            use m
            all_goals
            linarith [heq2]
          exact h_eq3
        have h5 : (2 * (x : ℤ) - 1) ∣ ((-6 * x ^ 2 + 26 * x - 12 : ℤ) - (2 * (x : ℤ) - 1) * (-3 * x + 11)) := by
          apply Dvd.dvd.sub
          exact h3
          have h800 : (2 * (x : ℤ) - 1) ∣ (2 * (x : ℤ) - 1) * (-3 * x + 11) := by
            use (-3 * x + 11)
            all_goals nlinarith
          exact h800
        -- from my previous manual calculation
        -- We compute $ -6x^2 + 26x -12 - (2x-1)(-3x +11) = x -1 $.
        have heq4 : ((-6 * x ^ 2 + 26 * x - 12 : ℤ) - (2 * (x : ℤ) - 1) * (-3 * x + 11)) = (x - 1 : ℤ) := by
          nlinarith
        rw [heq4] at h5
        exact h5
      have heq41 : (2 * (x : ℤ) - 1) > (0 : ℤ) := by
        omega
      have heq40 : (2 * (x : ℤ) - 1) ≤ (x - 1 : ℤ) := by
        exact Int.le_of_dvd (show (0 : ℤ) < (x - 1 : ℤ) by nlinarith) h10
      -- We need to show these are different.
      have heq42 : (x - 1 : ℤ) < (2 * (x : ℤ) - 1) := by
        omega
      linarith
    · -- so x ≤ 1.
      have heq30 : (x : ℤ) ≤ 1 := by omega
      -- Since x > 0, x = 1.
      have heq31 : (x : ℤ) = 1 := by
        omega
      exact heq31
  have hm : m = 8 := by
    rw [show (x : ℤ) = 1 by exact heq3] at heq
    omega
  exact hm