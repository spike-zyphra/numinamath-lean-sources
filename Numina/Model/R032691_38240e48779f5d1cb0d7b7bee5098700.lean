import Mathlib

theorem algebra_19511 (x : ℤ): (1 / 25 : ℝ) ^ (x + 2) = 125 ^ (-x) ↔ x = 4 := by
  constructor
  · -- Assume h $ means (1 / 25 : ℝ) ^ (x + 2) = 125 ^ (-x); prove x = 4.
    intro h
    have eq1 : (1 / 25 : ℝ) ^ (x + 2) = (5 ^ (-2 : ℤ) : ℝ) ^ (x + 2) := by
      norm_num
    have eq2 : (125 : ℝ) ^ (-x) = (5 ^ (3 : ℤ) : ℝ) ^ (-x) := by 
      norm_num
    rw [eq1, eq2] at h
    have eq3 : ((5 ^ (-2 : ℤ) : ℝ) ^ (x + 2) ) = ((5 : ℝ) ^ (-2 * (x + 2) : ℤ)) := by
      rw [← zpow_mul]
      all_goals ring_nf <;> norm_num
    have eq4 : ( (5 ^ (3 : ℤ) : ℝ) ^ (-x) ) = ((5 : ℝ) ^ (3 * (-x) : ℤ)) := by
      rw [← zpow_mul]
      all_goals ring_nf <;> norm_num
    rw [eq3, eq4] at h
    have eq5 : (5 : ℝ) ^ (-2 * (x + 2) : ℤ) = (5 : ℝ) ^ (3 * (-x) : ℤ) := by
      simpa using h
    have eq6 : -2 * (x + 2) = 3 * (-x) := by
      exact_mod_cast (by
        simpa using eq5
      )
    have eq7 : x = 4 := by
      linarith
    exact_mod_cast eq7
  · -- Assume x = 4 prove (1 / 25 : ℝ) ^ (x + 2) = 125 ^ (-x).
    intro h
    rw [h] 
    norm_num