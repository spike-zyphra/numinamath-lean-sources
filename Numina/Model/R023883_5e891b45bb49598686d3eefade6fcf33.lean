import Mathlib

theorem algebra_222377 (α : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 6)) (h₁ : Real.sin α ^ 6 + Real.cos α ^ 6 = 7 / 12) :
    1998 * Real.cos α = 333 * Real.sqrt 30 := by
  rcases h₀ with ⟨hα₁, hα₂⟩
  have h2 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : Real.cos α > 0 := by 
    apply Real.cos_pos_of_mem_Ioo 
    constructor <;> linarith [Real.pi_pos]
  have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h5 : Real.sin α ^ 2 * Real.cos α ^ 2 = 5 / 36 := by
    have h6 : Real.sin α ^ 6 + Real.cos α ^ 6 = (Real.sin α ^ 2 + Real.cos α ^ 2) ^ 3 - 3 * (Real.sin α ^ 2 * Real.cos α ^ 2) * (Real.sin α ^ 2 + Real.cos α ^ 2) := by 
      ring
    rw [h4] at h6 
    nlinarith 
  have h7 : (Real.cos α ^ 2 - 5 / 6) * (Real.cos α ^ 2 - 1 / 6) = 0 := by
    have h8 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by 
      linarith [h4]
    rw [h8] at h5 
    nlinarith
  cases' (mul_eq_zero.1 h7) with h8 h9
  · -- Case where $\cos^2 \alpha = \frac{5}{6}$
    have h10 : Real.cos α ^ 2 = 5 / 6 := by linarith 
    have h11 : 0 < Real.cos α := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have h12 : Real.cos α = Real.sqrt (5 / 6) := by 
      have h13 : Real.cos α > 0 := h11 
      have h14 : Real.cos α ^ 2 = 5 / 6 := h10 
      have h15 : Real.cos α = Real.sqrt (5 / 6) := by
        rw [← h14]
        field_simp 
      exact h15 
    have h13 : Real.sqrt (5 / 6) = Real.sqrt 30 / 6 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      <;> ring_nf <;> norm_num 
    rw [h12, h13] 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (30 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num)]
  · -- Case where $\cos^2 \alpha = \frac{1}{6}$
    have h14 : Real.cos α ^ 2 = 1 / 6 := by linarith 
    -- Show this leads to a contradiction with $\cos \alpha > \sqrt{3}/2$ for $\alpha \in (0, \pi/6)$
    have h11 : Real.cos α > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have h15 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six 
    have h16 : Real.cos α > Real.sqrt 3 / 2 := by
      have h17 : α < Real.pi / 6 := hα₂ 
      have h18 : Real.cos α > Real.cos (Real.pi / 6) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi 
        all_goals linarith [Real.pi_pos] 
      rw [h15] at h18 
      linarith 
    -- Compute $\sqrt{1/6} < \sqrt{3}/2$
    have h19 : Real.sqrt (1 / 6) < Real.sqrt 3 / 2 := by 
      have h19 : Real.sqrt (1 / 6) < Real.sqrt (3 / 4) := by 
        apply Real.sqrt_lt_sqrt 
        all_goals norm_num 
      have h20 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        <;> ring_nf 
        <;> norm_num 
      linarith [h20, h19] 
    -- Show $\cos \alpha = \sqrt{1/6}$ contradicts $\cos \alpha > \sqrt{3}/2$
    have h17 : Real.cos α = Real.sqrt (1 / 6) := by 
      have h11 : Real.cos α > 0 := h11 
      have h18 : Real.cos α ^ 2 = 1 / 6 := h14 
      have h19 : Real.cos α = Real.sqrt (1 / 6) := by 
        rw [← h18] 
        field_simp 
      exact h19 
    nlinarith [Real.sqrt_nonneg (1 / 6 : ℝ), Real.sqrt_nonneg (3 / 4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]