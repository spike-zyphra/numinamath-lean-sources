import Mathlib

theorem algebra_308364 {α β : ℝ} (h : α ≠ β) (h1 : α^2 - 3 * α + 1 = 0) (h2 : β^2 - 3 * β + 1 = 0)
    (h3 : α > β) : α^4 + 3 / β = 28 + 12 * √5 := by
  have h4 : α + β = 3 := by
    have h1' : α^2 - 3 * α + 1 = 0 := h1
    have h2' : β^2 - 3 * β + 1 = 0 := h2
    have eq1 : α^2 - 3 * α + 1 - (β^2 - 3 * β + 1) = 0 := by linarith
    have eq2 : (α - β) * (α + β - 3) = 0 := by
      ring_nf at eq1 ⊢
      linarith
    cases' (mul_eq_zero.mp eq2) with h5 h6
    · -- α - β = 0 implies α = β which is a contradiction
      exfalso
      apply h
      linarith
    · -- α + β - 3 = 0 implies α + β = 3
      linarith
  have h5 : α * β = 1 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h6
      apply h
      linarith), h4, sq_nonneg (α - β)]
  have h6 : α^2 = 3 * α - 1 := by
    nlinarith
  have h7 : α^4 = 21 * α - 8 := by
    calc
      α^4 = (α^2) ^ 2 := by ring
      _ = (3 * α - 1) ^ 2 := by rw [h6]
      _ = 9 * α^2 - 6 * α + 1 := by ring
      _ = 9 * (3 * α - 1) - 6 * α + 1 := by rw [h6]
      _ = 21 * α - 8 := by linarith
  have h8 : 3 / β = 3 * α := by
    have h9 : β ≠ 0 := by
      by_contra h0
      have h0' : β = 0 := by linarith
      rw [h0'] at h5
      nlinarith
    have h10 : α ≠ 0 := by
      by_contra h0
      have h0' : α = 0 := by linarith
      rw [h0'] at h5
      nlinarith
    field_simp [h9]
    nlinarith [h5]
  have h9 : α^4 + 3 / β = 24 * α - 8 := by
    linarith [h7, h8]
  have h10 : α^2 - 3 * α + 1 = 0 := h1
  have h11 : α = (3 + Real.sqrt 5) / 2 := by
    have h12 : α^2 - 3 * α + 1 = 0 := h1
    have h13 : (α - (3 + Real.sqrt 5) / 2) * (α - (3 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_pos_of_ne_zero (show (α - β) ≠ 0 by
        intro h6
        apply h
        linarith
      ), h4, h3]
    cases' (mul_eq_zero.mp h13) with h14 h15
    · -- $\alpha = \frac{3 + \sqrt{5}}{2}$.
      linarith
    · -- $\alpha = \frac{3 - \sqrt{5}}{2}$.
      exfalso
      have h16 : β = (3 + Real.sqrt 5) / 2 := by
        have h2' : β^2 - 3 * β + 1 = 0 := h2
        have h17 : (β - (3 + Real.sqrt 5) / 2) * (β - (3 - Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_pos_of_ne_zero (show (α - β) ≠ 0 by
            intro h6
            apply h
            linarith
          ), h4, h3]
        cases' (mul_eq_zero.mp h17) with h18 h19
        · -- $\beta = \frac{3 + \sqrt{5}}{2}$. 
          linarith
        · -- $\beta = \frac{3 - \sqrt{5}}/2$. 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3, h4]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3, h4, sq_nonneg (α - β)]
  rw [h9, h11]
  field_simp
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]