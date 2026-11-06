import Mathlib

theorem algebra_250292 :
    {x : ℝ | (2 * x + 3)^2 + (3 * x - 5)^2 - Real.sqrt (13 * x^2 - 18 * x + 20) = 44 ∧ 
            13 * x^2 - 18 * x + 20 ≥ 0} = 
    {2, -8/13} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x satisfies the equation
    rintro ⟨h1, h2⟩
    have h3 : (2 * x + 3) ^ 2 + (3 * x - 5) ^ 2 - Real.sqrt (13 * x ^ 2 - 18 * x + 20) = 44 := h1
    have eq1 : 13 * x^2 - 18 * x - 10 = Real.sqrt (13 * x^2 - 18 * x + 20) := by 
      nlinarith 
    have eq2 : (13 * x^2 - 18 * x - 10) ^ 2 = Real.sqrt (13 * x^2 - 18 * x + 20) ^ 2 := by 
      rw [eq1]
    have eq3 : Real.sqrt (13 * x^2 - 18 * x + 20) ^ 2 = 13 * x^2 - 18 * x + 20 := Real.sq_sqrt (by linarith)
    rw [eq3] at eq2
    have h5 : (13 * x^2 - 18 * x - 10) ^ 2 - (13 * x^2 - 18 * x + 20) = 0 := by nlinarith [eq2]
    have h6 : (13 * x^2 - 18 * x - 16) * (13 * x^2 - 18 * x - 5) = 0 := by 
      nlinarith [h5]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- First factor equals zero: $13 x^2 - 18 x - 16 = 0$
      have h8 : (13 * x + 8) * (x - 2) = 0 := by 
        nlinarith [h7]
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- Case $13x+8=0$
        right
        linarith 
      · -- Case $x-2=0$
        left 
        linarith
    · -- Second factor equals zero: $13 x^2 - 18 x - 5 = 0$
      nlinarith [Real.sqrt_nonneg (13 * x^2 - 18 * x + 20), Real.sq_sqrt (show 0 ≤ 13 * x^2 - 18 * x + 20 by linarith), sq_nonneg (Real.sqrt (13 * x^2 - 18 * x + 20) - 6), sq_nonneg (x - 2), sq_nonneg (x + 8/13)]
  · -- Show that 2 and -8/13 satisfy the equation 
    rintro (h | h)
    · -- Case x = 2 
      rw [h] 
      constructor
      · -- First part: Check equality 
        have h1 : Real.sqrt (13 * (2 : ℝ) ^ 2 - 18 * (2 : ℝ) + 20) = (6 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        nlinarith [h1]
      · -- Second part: Check non-negative 
        norm_num 
    · -- Case x = -8/13 
      rw [h] 
      constructor 
      · -- First part: Check equality 
        have h1 : Real.sqrt (13 * (-8 / 13 : ℝ) ^ 2 - 18 * (-8 / 13 : ℝ) + 20) = (6 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        nlinarith [h1] 
      · -- Second part: Check non-negative 
        norm_num