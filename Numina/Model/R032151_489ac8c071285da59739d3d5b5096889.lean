import Mathlib

theorem algebra_301185 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 2*x^2+6*x*y-12*x*z+x-3*y+6*z-6=0) :
    ∃ t, x=3 ∧ y=2*t-1 ∧ z=t ∨ x=1 ∧ y=2*t+1 ∧ z=t := by
  have h1 : 2 * x ^ 2 + 6 * x * y - 12 * x * z + x - 3 * y + 6 * z - 6 = 0 := h
  have h2 : 2 * x ^ 2 + x - 6 + (2 * x - 1) * (3 * y - 6 * z) = 0 := by 
    nlinarith [h]
  have h3 : (2 * x - 1) * (3 * y - 6 * z) = -2 * x ^ 2 - x + 6 := by 
    linarith [h2]
  have h4 : (2 * x - 1) * (3 * (y - 2 * z)) = (2 * x - 1) * (3 * y - 6 * z) := by 
    ring_nf
  have h5 : (2 * x - 1) * (3 * (y - 2 * z)) = -2 * x ^ 2 - x + 6 := by
    linarith [h3, h4]
  have h6 : (2 * x - 1) ∣ 5 := by
    have h7 : (2 * x - 1) ∣ -2 * x ^ 2 - x + 6 := by
      use 3 * (y - 2 * z)
      linarith [h5]
    have h8 : (2 * x - 1) ∣ 5 := by
      have h9 : -2 * x ^ 2 - x + 6 = -(2 * x - 1) * (x + 1) + 5 := by
        nlinarith [sq_nonneg (x)]
      rw [h9] at h7
      have h10 : (2 * x - 1) ∣ (-(2 * x - 1) * (x + 1)) := by
        use -(x + 1)
        all_goals nlinarith
      have h11 : (2 * x - 1) ∣ 5 := by
        have h10' : (2 * x - 1) ∣ (-(2 * x - 1) * (x + 1)) := h10
        have h11' : (2 * x - 1) ∣ ((-(2 * x - 1) * (x + 1)) + 5) := by
          exact h7
        have h12 : (2 * x - 1) ∣ 5 := by
          have h13 : (2 * x - 1) ∣ (5) := by
            have h14 : (2 * x - 1) ∣ ((-(2 * x - 1) * (x + 1)) + 5) := by assumption
            have h15 : (2 * x - 1) ∣ (-(2 * x - 1) * (x + 1)) := by assumption
            have h16 : (2 * x - 1) ∣ (((-(2 * x - 1) * (x + 1)) + 5) - (-(2 * x - 1) * (x + 1))) := by
              apply dvd_sub
              assumption
              assumption
            have h17 : (((-(2 * x - 1) * (x + 1)) + 5) - (-(2 * x - 1) * (x + 1))) = 5 := by
              linarith
            rw [h17] at h16
            exact h16
          exact h13
        exact h12
      exact h11
    exact h8
  have h7 : (2 * x - 1) = 1 ∨ (2 * x - 1) = 5 := by
    have h8 : (2 * x - 1) ∣ 5 := h6
    have h9 : (2 * x - 1) > 0 := by
      have hpos : 0 < x := hx
      have : 2 * x - 1 > 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y - 2 * z), sq_nonneg (x - 1), sq_nonneg (x - 3)]
      linarith
    have h10 : (2 * x - 1) ≤ 5 := by
      apply Int.le_of_dvd (by norm_num) h8
      all_goals nlinarith
    interval_cases k : (2 * x - 1) <;> omega
  rcases h7 with h7 | h7
  · -- When 2x-1 = 1, so x = 1
    have hx1 : x = 1 := by
      omega
    have hy1 : 3 * (y - 2 * z) = 3 := by
      rw [show 2 * x - 1 = 1 by omega] at h5
      nlinarith
    have h13 : y = 2 * z + 1 := by
      omega
    use z
    right
    constructor
    · exact hx1
    constructor
    · -- Show that y = 2*t + 1 where t = z
      linarith [h13]
    · -- z = t 
      rfl
  · -- When 2x-1 = 5, so x = 3
    have hx3 : x = 3 := by
      omega
    have hy3 : 3 * (y - 2 * z) = -3 := by
      rw [show 2 * x - 1 = 5 by omega] at h5
      nlinarith
    have h14 : y = 2 * z - 1 := by
      omega
    use z
    left
    constructor
    · exact hx3
    constructor
    · -- Show that y = 2*t - 1 where t = z
      linarith [h14]
    · -- z = t 
      rfl