import Mathlib

theorem algebra_278322 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ x : ℝ, a * x ^ 2 + b * x + c = 0 → |x| ≤ (2 * |a * c| + b ^ 2) / |a * b| := by
  intro x h_eq
  have h1 : a * x ^ 2 + b * x + c = 0 := h_eq
  have h2 : c = -a * x^2 - b * x := by
    have h3 : a * x ^ 2 + b * x + c = 0 := h1
    linarith
  have h3 : a * b ≠ 0 := mul_ne_zero ha hb
  have h4 : |a * b| > 0 := by
    apply abs_pos.mpr
    exact h3
  have h5 : |x| ≤ (2 * |a * c| + b ^ 2) / |a * b| := by
    have h6 : |x| * |a * b| ≤ 2 * |a * c| + b ^ 2 := by
      have h9 : |a * c| = |a * (-a * x ^ 2 - b * x)| := by 
        rw [h2]
        <;> simp [abs_mul]
      have h10 : |a * (-a * x ^ 2 - b * x)| = |a ^ 2 * x ^ 2 + a * b * x| := by
        have h14 : a * (-a * x ^ 2 - b * x) = -a ^ 2 * x ^ 2 - a * b * x := by ring
        rw [h14]
        have h12 : |-a^2 * x ^ 2 - a * b * x| = |a^2 * x ^ 2 + a * b * x| := by
          have h14 : -a^2 * x ^ 2 - a * b * x = -(a^2 * x ^ 2 + a * b * x) := by ring
          rw [h14]
          rw [abs_neg]
        linarith [h12]
      have h11 : |a * b * x| = |a * b| * |x| := by
        rw [abs_mul]
        <;> simp [abs_mul]
      have h13 : |a * b * x| ≤ 2 * |a ^ 2 * x ^ 2 + a * b * x| + b ^ 2 := by
        cases' abs_cases (a * b * x) with h h <;> 
          cases' abs_cases (a ^ 2 * x ^ 2 + a * b * x) with k k <;> 
            cases' abs_cases (a) with ha' ha' <;> 
              cases' abs_cases (b) with hb' hb' <;> 
                try { 
                  nlinarith [sq_nonneg (x * a + b / 2), sq_nonneg (x * a ^ 2 * b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (x), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
                }
      have h14 : |a * c| = |a ^ 2 * x ^ 2 + a * b * x| := by 
        rw [h9]
        linarith [h10]
      nlinarith [abs_nonneg (a * b * x), abs_nonneg (a ^ 2 * x ^ 2 + a * b * x), h11, h14, h13]
    have h4 : |a * b| > 0 := h4
    have h7 : |x| ≤ (2 * |a * c| + b ^ 2) / |a * b| := by
      apply (le_div_iff₀ h4).mpr
      linarith [h6]
    linarith [h7]
  linarith [h5]