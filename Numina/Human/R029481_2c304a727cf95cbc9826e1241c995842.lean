import Mathlib

/- Solve the equation $x = \sqrt{x - \frac{1}{x}} + \sqrt{1 - \frac{1}{x}}$ for $x$. -/
theorem algebra_8544 {x : ℝ} (hx : 1 ≤ x) : x = Real.sqrt (x - 1 / x) + Real.sqrt (1 - 1 / x) ↔
    x = (1 + Real.sqrt 5) / 2 := by
    have l1: x⁻¹ ≤ 1 := by  -- show a simple inequality
        rw [inv_le_one_iff₀]
        right
        linarith
    constructor
    -- forward direction
    . intro h
      replace h: x -  √(x - 1 / x) = √(1 - 1 / x) := by
         nth_rewrite 1 [h]
         ring
      replace h: (x -  √(x - 1 / x)) ^ 2 = (√(1 - 1 / x)) ^ 2 := by  -- square first time
        rw [h]
      have o1: (x -  √(x - 1 / x)) ^ 2 = x ^ 2 - 2 * x * √(x - 1 / x) + (x - 1 / x) := by
        ring_nf
        have o: √(x - x⁻¹) ^ 2 = x - x⁻¹ := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          simp
          nlinarith
          apply Real.sqrt_nonneg
        rw [o]
        ring
      have o2: (√(1 - 1 / x)) ^ 2 = 1 - 1 / x := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        simp
        rw [inv_le_one_iff₀]
        right
        exact hx
        apply Real.sqrt_nonneg
      rw [o1, o2] at h
      clear o1 o2
      replace h: x ^ 2 + x - 1 = 2 * x * √(x - 1 / x) := by
        nlinarith
      replace h: (x ^ 2 + x - 1) ^ 2  = (2 * x * √(x - 1 / x)) ^ 2 := by  -- square second time
        rw [h]
      ring_nf at h
      have o: √(x - x⁻¹) ^ 2 = x - x⁻¹ := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        simp
        nlinarith
        apply Real.sqrt_nonneg
      rw [o] at h
      clear o
      field_simp at h -- remove the denominator
      replace h: x ^ 4 - 2 * x ^ 3 - x ^ 2 + 2 * x + 1 = 0 := by nlinarith
      have eq: x ^ 4 - 2 * x ^ 3 - x ^ 2 + 2 * x + 1 = (x ^ 2 - x - 1) ^ 2:= by ring  --factor the polynomial
      rw [eq] at h
      clear eq
      simp at h
      have eq: x ^ 2 - x - 1 = (x - (1 + √5) / 2) * (x - (1 - √5) / 2) := by
        ring_nf
        have o: √5 ^ 2 = 5 := by
          norm_num
        rw [o]
        ring_nf
      rw [eq] at h -- factor the quadratic polynomial
      simp at h
      rcases h with h | h
      . linarith
      . replace h: 2 * x = (1 - √5) := by linarith
        have o: 1 - √5 ≤ 1 := by
          simp
        rw [← h] at o
        nlinarith
    -- backward direction
    . intro h
      have f: 1 / x = x - 1 := by -- now we have x ^ 2 - x - 1 = 0
        field_simp
        simp [h]
        ring_nf
        have o: √5 ^ 2 = 5 := by
          norm_num
        rw [o]
        ring
      simp [f]
      ring_nf
      have o: x - 1 = √(2 - x) := by
        symm
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
        . ring_nf
          replace f: x ^ 2 = x + 1 := by
            field_simp at f
            nlinarith
          simp [f]
          ring
        . simp [h]
          have o: 1 < √5 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          nlinarith
      rw [← o]
      simp
