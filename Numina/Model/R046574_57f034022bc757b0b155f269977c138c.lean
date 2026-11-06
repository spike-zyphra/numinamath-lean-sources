import Mathlib

theorem algebra_165764 {n : ℕ} (hn : n > 0) :
    ∃ x : ℚ, x^n + (2 + x)^n + (2 - x)^n = 0 ↔ n = 1 := by
  by_cases h : n = 1
  · -- If n = 1, then the equation has a solution at x = -4
    use -4
    simp [h]
    <;> norm_num
  · -- If n > 1, then there is no rational solution
    have h2 : n > 1 := by
      by_contra h'
      push_neg at h'
      have : n = 1 := by
        linarith
      contradiction
    use (0 : ℚ)
    have h_eq0 : ((0 : ℚ) : ℚ) ^ n + (2 + (0 : ℚ)) ^ n + (2 - (0 : ℚ)) ^ n = 0 ↔ n = 1 := by
      have eq1 : ((0 : ℚ) : ℚ) ^ n + (2 + (0 : ℚ)) ^ n + (2 - (0 : ℚ)) ^ n = (0 : ℚ) ^ n + ((2 : ℚ) ) ^ n + ((2 : ℚ) ) ^ n := by
        ring
      rw [eq1] at *
      have h3 : n ≥ 2 := by
        omega
      have eq2 : ((0 : ℚ) : ℚ) ^ n = (0 : ℚ) := by
        have : n ≥ 2 := h3
        have eq3 : ((0 : ℚ) : ℚ) ^ n = ((0 : ℚ) : ℚ) ^ 2 * ((0 : ℚ) : ℚ) ^ (n - 2) := by
          rw [show n = 2 + (n - 2) by omega]
          rw [pow_add]
          all_goals norm_num
          <;> omega
        rw [eq3]
        norm_num
        <;> nlinarith
      have eq3 : (0 : ℚ) ^ n + ((2 : ℚ) ) ^ n + ((2 : ℚ) ) ^ n = (0 : ℚ) + ((2 : ℚ) ) ^ n + ((2 : ℚ) ) ^ n := by
        rw [eq2]
      rw [eq3] at *
      constructor
      · -- Assume the equation holds, prove n = 1
        intro h_eq
        have eq4 : (0 : ℚ) + ((2 : ℚ) ) ^ n + ((2 : ℚ) ) ^ n = 0 := by
          linarith [h_eq]
        have eq6 : ((2 : ℚ) ) ^ n + ((2 : ℚ) ) ^ n = 0 := by
          linarith
        have eq7 : ((2 : ℚ) ) ^ n > 0 := by positivity
        nlinarith [eq6, eq7]
      · -- Assume n = 1, prove the equation holds
        intro h_eq
        omega
    exact h_eq0