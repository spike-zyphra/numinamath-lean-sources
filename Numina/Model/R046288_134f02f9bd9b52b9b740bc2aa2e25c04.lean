import Mathlib

theorem algebra_10652 : {x : ℝ | 0 ≤ x ∧ (x * Real.sqrt (x ^ 3)) ^ ((1 : ℝ) / 5) = 3} = {9} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that the condition implies x = 9
    intro h
    rcases h with ⟨hx1, heq⟩
    have h2 : ((x * Real.sqrt (x ^ 3)) ^ ((1 : ℝ) / 5) ) = 3 := by
      simpa using heq
    have h3 : (x * Real.sqrt (x ^ 3)) = 243 := by
      have h4 : ((x * Real.sqrt (x ^ 3)) ^ ((1 : ℝ) / 5) ) = (3 : ℝ) := h2
      have h5 : ((x * Real.sqrt (x ^ 3)) ^ ((1 : ℝ) / 5) ) ^ (5 : ℝ) = (3 : ℝ) ^ (5 : ℝ) := by 
        rw [h4]
      -- Simplify left side using Real.rpow_mul
      have h6 : ((x * Real.sqrt (x ^ 3)) ^ ((1 : ℝ) / 5) ) ^ (5 : ℝ) = x * Real.sqrt (x ^ 3) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith [show 0 ≤ x * Real.sqrt (x ^ 3) from by positivity]
      rw [h6] at h5
      -- Simplify right side
      have h7 : (3 : ℝ) ^ (5 : ℝ) = (243 : ℝ) := by
        norm_num
      rw [h7] at h5
      linarith
    have h4 : x = 9 := by
      by_cases h5 : x > 0
      · -- Case : x > 0
        have h7 : Real.sqrt (x ^ 3) = x * Real.sqrt x := by
          have h8 : Real.sqrt (x^3) = Real.sqrt (x^2 * x) := by ring_nf
          rw [h8]
          have h9 : Real.sqrt (x^2 * x) = Real.sqrt (x^2) * Real.sqrt x := by
            rw [Real.sqrt_mul (by nlinarith)]
          rw [h9]
          have h10 : Real.sqrt (x^2) = x := by
            rw [Real.sqrt_sq (by linarith)]
          rw [h10]
        have h8 : x * Real.sqrt (x ^ 3) = x^2 * Real.sqrt x := by
          rw [h7]
          ring
        have h9 : x^2 * Real.sqrt x = x ^ (5 / 2 : ℝ) := by
          have h10 : x ^ (5 / 2 : ℝ) = x^2 * Real.sqrt x := by
            have h11 : x ^ (5 / 2 : ℝ) = (x ^ (2 : ℝ)) * (x ^ (1 / 2 : ℝ)) := by
              rw [← Real.rpow_add]
              norm_num
              all_goals linarith [show x > 0 by linarith]
            have h12 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
              norm_cast
            have h13 : x ^ (2 : ℕ) = (x^2) := by
              simp
            rw [h12, h13] at h11
            have h14 : x ^ (1 / 2 : ℝ) = Real.sqrt x := by
              rw [← Real.sqrt_eq_rpow]
            rw [h14] at h11
            linarith
          linarith
        rw [h8] at h3
        rw [h9] at h3
        have h11 : x ^ (5 / 2 : ℝ) = 243 := by
          linarith
        -- From $x ^ {5 / 2} = 243$ to $x = 9$.
        have h12 : x = (x ^ (5 / 2 : ℝ) ) ^ (2 / 5 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            nlinarith [show x > 0 by linarith]
        rw [h12, h11]
        have h13 : ( (243 : ℝ) ) ^ (2 / 5 : ℝ) = (9 : ℝ) := by
          have h14 : ( (243 : ℝ) ) ^ (2 / 5 : ℝ) = (3 ^ (5 : ℝ) ) ^ (2 / 5 : ℝ) := by
            norm_num
          rw [h14]
          have h15 : ( (3 : ℝ) ^ (5 : ℝ) ) ^ (2 / 5 : ℝ) = (3 : ℝ) ^ (5 * (2 / 5) : ℝ) := by
            rw [← Real.rpow_mul]
            ring
            all_goals
              nlinarith
          rw [h15]
          norm_num
          all_goals nlinarith
        rw [h13]
        all_goals linarith
      · -- Case x ≤ 0, so x = 0
        have h51 : x = 0 := by
          linarith [show x ≥ 0 by linarith, show ¬(x > 0) by linarith]
        rw [h51] at h3
        nlinarith
    exact h4
  · -- Second direction: if x = 9, prove the conditions
    intro heq
    rw [heq]
    constructor
    · norm_num
    · -- Verify the equation
      have h1 : ((9 * Real.sqrt (9 ^ 3)) ^ ((1 : ℝ) / 5) ) = 3 := by
        have h2 : Real.sqrt (9 ^ 3) = 27 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h2]
        have h3 : ( (9 * (27 : ℝ) ) ) = (243 : ℝ) := by norm_num
        rw [h3]
        have h4 : ( (243 : ℝ) ) ^ ((1 : ℝ) / 5) = (3 : ℝ) := by
          have h5 : (243 : ℝ) ^ ((1 : ℝ) / 5) = (3 ^ (5 : ℝ) ) ^ ((1 : ℝ) / 5) := by
            norm_num
          rw [h5]
          have h6 : ( (3 : ℝ) ^ (5 : ℝ) ) ^ ((1 : ℝ) / 5) = (3 : ℝ) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          rw [h6]
        exact h4
      exact h1