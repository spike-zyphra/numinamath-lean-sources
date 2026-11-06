import Mathlib

theorem number_theory_241711 (a b : ℕ) (h : 2019 = a^2 - b^2) (ha : a < 1000) :
    a = 338 := by
  by_cases h5 : b < a
  · -- Assume b < a
    have h6 : a^2 - b^2 = 2019 := by
      omega
    have h7 : (a : ℕ) ≤ 999 := by linarith
    have h8 : (a - b) * (a + b) = 2019 := by
      have h14 : a ≥ b := by
        nlinarith [h5]
      have h15 : a^2 - b^2 = 2019 := by
        omega
      have h16 : (a^2 - b^2 : ℕ) = (a - b) * (a + b) := by
        rw [Nat.sq_sub_sq]
        all_goals linarith
      have h17 : (a^2 - b^2 : ℕ) = (2019 : ℕ) := by
        omega
      linarith
    have h10 : (a - b) ∣ 2019 := by
      use (a + b)
      all_goals linarith
    have h11 : (a - b) ∣ 2019 := by
      use (a + b)
      all_goals nlinarith
    have h12 : (a - b) ∣ 2019 := by
      use (a + b)
      all_goals nlinarith
    have h13 : (a - b) ≤ 2019 := by
      exact Nat.le_of_dvd (show 0 < 2019 by norm_num) h12
    interval_cases h14 : a - b <;> omega
  · -- Assume not b < a, so b ≥ a
    have h10 : b ≥ a := by
      omega
    have h11 : a ≤ b := by
      omega
    have h12 : (a^2 : ℕ) - (b^2 : ℕ) ≤ 0 := by
      have h3 : a^2 ≤ b^2 := by
        nlinarith [h11]
      omega
    omega