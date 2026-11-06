import Mathlib

theorem algebra_260363 (x y z : ℤ) (h1 : x + y + z = 2) (h2 : x^3 + y^3 + z^3 = -10) :
    (x = 3 ∧ y = 3 ∧ z = -4) ∨ (x = 3 ∧ y = -4 ∧ z = 3) ∨ (x = -4 ∧ y = 3 ∧ z = 3) := by
  have h3 : z = 2 - x - y := by
    omega 
  rw [h3] at h2
  have h4 : (x + y) * (x * y - 2 * (x + y) + 4) = 6 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (2 - x - y)), sq_nonneg (x - (2 - x - y))]

  have h7 : (x + y) = 1 ∨ (x + y) = 2 ∨ (x + y) = 3 ∨ (x + y) = 6 ∨ (x + y) = -1 ∨ (x + y) = -2 ∨ (x + y) = -3 ∨ (x + y) = -6 := by
    have h8 : (x + y) ∣ 6 := by
      use (x * y - 2 * (x + y) + 4)
      all_goals 
        linarith [h4]
    have h9 : (x + y) ≤ 6 := by 
      exact Int.le_of_dvd (show 0 < (6 : ℤ) by norm_num) h8 
    have h10 : (x + y) ≥ -6 := by 
      have h11 : -(x + y) ∣ 6 := by
        exact Int.neg_dvd.2 h8
      have h12 : -(x + y) ≤ 6 := by 
        exact Int.le_of_dvd (show 0 < (6 : ℤ) by norm_num) h11 
      omega
    interval_cases (x + y) <;> tauto

  rcases h7 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8)

  · -- Case $s = 1$
    have h10 : x + y = 1 := by linarith 
    have h11 : x * y = 4 := by 
      rw [show x + y = 1 by linarith] at h4
      nlinarith
    have h12 : (x - y) ^ 2 < (0 : ℤ) := by
      nlinarith [sq_nonneg (x - y)]
    nlinarith [sq_nonneg (x - y)]

  · -- Case $s = 2$
    have h10 : x + y = 2 := by linarith 
    have h11 : x * y = 3 := by 
      rw [show x + y = 2 by linarith] at h4
      nlinarith
    have h12 : (x - y) ^ 2 < (0 : ℤ) := by
      nlinarith [sq_nonneg (x - y)]
    nlinarith [sq_nonneg (x - y)]

  · -- Case $s = 3$
    have h10 : x + y = 3 := by linarith 
    have h11 : x * y = 4 := by 
      rw [show x + y = 3 by linarith] at h4
      nlinarith
    have h12 : (x - y) ^ 2 < (0 : ℤ) := by
      nlinarith [sq_nonneg (x - y)]
    nlinarith [sq_nonneg (x - y)]

  · -- Case $s = 6$
    have h10 : x + y = 6 := by linarith 
    have h11 : x * y = 9 := by 
      rw [show x + y = 6 by linarith] at h4
      nlinarith
    have h12 : (x - y) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y)]
    have h13 : x = y := by 
      nlinarith 
    have h14 : x = 3 := by 
      nlinarith 
    have h15 : y = 3 := by 
      linarith 
    have h16 : z = -4 := by 
      nlinarith [show z = 2 - x - y by linarith, h14, h15] 
    left 
    exact ⟨by linarith, by linarith, by linarith⟩

  · -- Case $s = -1$
    have h10 : x + y = -1 := by linarith 
    have h11 : x * y = -12 := by 
      rw [show x + y = -1 by linarith] at h4
      nlinarith 
    have h12 : (x - 3) * (x + 4) = 0 := by
      have h31 : y = -1 - x := by 
        nlinarith 
      rw [show y = -1 - x by linarith] at h11 
      nlinarith 
    cases' (mul_eq_zero.1 h12) with h14 h15 
    · -- When $x = 3$ 
      have h16 : x = 3 := by linarith 
      have h17 : y = -4 := by 
        nlinarith 
      have h18 : z = 3 := by 
        nlinarith [show z = 2 - x - y by linarith, h16, h17] 
      right 
      left 
      exact ⟨by linarith, by linarith, by linarith⟩ 
    · -- When $x = -4$ 
      have h16 : x = -4 := by linarith 
      have h17 : y = 3 := by 
        nlinarith 
      have h18 : z = 3 := by 
        nlinarith [show z = 2 - x - y by linarith, h16, h17] 
      right 
      right 
      exact ⟨by linarith, by linarith, by linarith⟩

  · -- When $s = -2$
    have h10 : x + y = -2 := by linarith 
    have h11 : x * y = -11 := by 
      rw [show x + y = -2 by linarith] at h4
      nlinarith 
    exfalso 
    have h12 : (x - y) ^ 2 = 48 := by 
      nlinarith 
    have h13 : (x - y) ^ 2 = 48 := by
      nlinarith 
    have h14 : (x - y) ≤ 6 := by nlinarith 
    have h15 : (x - y) ≥ -7 := by nlinarith 
    interval_cases (x - y) <;> omega

  · -- When $s = -3$
    have h10 : x + y = -3 := by linarith 
    have h11 : x * y = -12 := by 
      rw [show x + y = -3 by linarith] at h4
      nlinarith 
    exfalso 
    have h12 : (x - y) ^ 2 = 57 := by 
      nlinarith 
    have h13 : (x - y) ^ 2 = 57 := by
      nlinarith 
    have h14 : (x - y) ≤ 7 := by nlinarith 
    have h15 : (x - y) ≥ -7 := by nlinarith 
    interval_cases (x - y) <;> omega

  · -- When $s = -6$
    have h10 : x + y = -6 := by linarith 
    have h11 : x * y = -17 := by 
      rw [show x + y = -6 by linarith] at h4
      nlinarith 
    exfalso 
    have h12 : (x - y) ^ 2 = 104 := by 
      nlinarith 
    have h13 : (x - y) ^ 2 = 104 := by
      nlinarith 
    have h14 : (x - y) ≤ 10 := by nlinarith 
    have h15 : (x - y) ≥ -10 := by nlinarith 
    interval_cases (x - y) <;> omega