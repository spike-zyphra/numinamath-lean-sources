import Mathlib

theorem algebra_252086 (x : ℝ) (hx : x ∈ Set.Icc 1 4) :
    Real.sqrt ((x - 1)^2 * (x - 4)) = abs (x - 1) * Real.sqrt (16 - x^2) ↔ x = 1 ∨ x = 4 := by
  rw [Set.mem_Icc] at hx
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Assume the equation holds, prove x = 1 or x = 4
    intro h
    have h3 : (x - 1) ^ 2 * (x - 4) ≥ 0 := by
      by_contra h4
      push_neg at h4
      have h4' : Real.sqrt ((x - 1) ^ 2 * (x - 4)) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
        all_goals nlinarith
      rw [h4'] at h
      have h5 : abs (x - 1) * Real.sqrt (16 - x^2) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- abs (x - 1) = 0
        have h8 : abs (x - 1) = 0 := by
          linarith
        have : x - 1 = 0 := by
          simpa [abs_eq_zero] using h8
        nlinarith
      · -- Real.sqrt (16 - x^2) = 0
        have h8 : Real.sqrt (16 - x^2) = 0 := by
          linarith
        have h9 : 16 - x^2 = 0 := by
          rw [Real.sqrt_eq_zero (by nlinarith)] at h8
          linarith
        nlinarith
    have h4 : (16 - x^2) ≥ 0 := by
      by_contra h5
      push_neg at h5
      have h6 : Real.sqrt (16 - x^2) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
        all_goals nlinarith
      rw [h6] at h
      have h5 : abs (x - 1) * (0 : ℝ) = 0 := by
        nlinarith
      all_goals nlinarith
    have eqn : (x - 1) ^ 2 * (x - 4) = (abs (x - 1)) ^ 2 * (16 - x^2) := by
      calc
        (x - 1) ^ 2 * (x - 4) = (Real.sqrt ((x - 1) ^ 2 * (x - 4))) ^ 2 := by rw [Real.sq_sqrt (by nlinarith)]
        _ = (abs (x - 1) * Real.sqrt (16 - x^2)) ^ 2 := by rw [h]
        _ = (abs (x - 1)) ^ 2 * (Real.sqrt (16 - x^2) ) ^ 2 := by ring_nf
        _ = (abs (x - 1)) ^ 2 * (16 - x^2) := by rw [Real.sq_sqrt (by nlinarith)]
    by_cases h5 : (x - 1 : ℝ) = 0
    · -- If x - 1 = 0, then x = 1, which is our first solution
      have hx1' : x = 1 := by linarith
      left
      exact hx1'
    · -- If x - 1 ≠ 0, we can divide both sides by (x - 1)^2
      have h6 : (abs (x - 1)) ^ 2 = (x - 1) ^ 2 := by
        rw [sq_abs]
      rw [h6] at eqn
      have h7 : (x - 4) = (16 - x ^ 2) := by
        apply (mul_left_inj' (show (x - 1 : ℝ) ^ 2 ≠ 0 by
          have h5' : (x - 1 : ℝ) ≠ 0 := by
            intro h6
            apply h5
            linarith
          have : (x - 1) ^ 2 ≠ 0 := by
            apply pow_ne_zero 2
            exact h5'
          assumption
        )).mp
        nlinarith
      have h8 : x^2 + x - 20 = 0 := by
        nlinarith
      have h9 : (x - 4) * (x + 5) = 0 := by 
        ring_nf at h8 ⊢
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- Case x - 4 = 0, so x = 4
        have hx4 : x = 4 := by
          linarith
        right
        linarith
      · -- Case x + 5 = 0, so x = -5
        have hx2 : x = -5 := by
          nlinarith
        nlinarith
  · -- Backward direction: if x = 1 or x = 4, then the equation holds
    rintro (h | h)
    · -- Case x = 1
      rw [h]
      norm_num
      <;> ring_nf <;> norm_num
    · -- Case x = 4
      rw [h]
      norm_num
      <;> ring_nf <;> norm_num