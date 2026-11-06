import Mathlib

theorem algebra_10342 {f : ℝ → ℝ} (hf : ∀ x ≠ 0, f x = f 1 * x + f 2 / x - 1) :
    IsLeast {y | ∃ x > 0, f x = y} (Real.sqrt 3 - 1) := by

  have f2_eq_1 : f 2 = 1 := by
    have eq1 := hf 1 (by norm_num)
    norm_num at eq1 
    have eq2 := hf 2 (by norm_num)
    norm_num at eq2 
    linarith
  
  have f1_eq_3_div_4 : f 1 = 3 / 4 := by
    have eq1 := hf 1 (by norm_num)
    norm_num at eq1 
    have eq2 := hf 2 (by norm_num)
    norm_num at eq2 
    rw [f2_eq_1] at eq2 
    linarith

  constructor 
  · -- Show that there exists some x > 0 such that f x = Real.sqrt 3 - 1
    use 2 * Real.sqrt 3 / 3 
    constructor 
    · -- Show that x > 0
      positivity 
    · -- Show that f x = Real.sqrt 3 - 1 
      have eq3 : ∀ x ≠ 0, f x = f 1 * x + f 2 / x - 1 := by 
        intro x hx
        apply hf x hx 
      specialize eq3 (2 * Real.sqrt 3 / 3) (by 
        -- Show 2 * Real.sqrt 3 / 3 ≠ 0 
        positivity 
      )
      rw [eq3]
      rw [f1_eq_3_div_4, f2_eq_1]
      field_simp 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  · -- Show that Real.sqrt 3 - 1 is minimal 
    intro y hy
    rcases hy with ⟨x, hx, heq⟩ 
    have hx_ne_zero : x ≠ 0 := by linarith 
    have hx1 := hf x hx_ne_zero 
    rw [hx1] at heq 
    have h1 : f 1 = 3 / 4 := f1_eq_3_div_4 
    have h2 : f 2 = 1 := f2_eq_1 
    rw [h1, h2] at heq 
    -- We need to show that Real.sqrt 3 - 1 ≤ f x 
    -- which is Real.sqrt 3 - 1 ≤ (3/4) x + 1/x - 1 
    -- equivalent to Real.sqrt 3 ≤ (3/4) x + 1/x 
    have h3 : (3 / 4) * x + 1 / x ≥ Real.sqrt 3 := by
      have h4 : ( (3 / 4) * x + 1 / x ) - Real.sqrt 3 ≥ 0 := by
        have hx1_pos : x > 0 := hx
        have h5 : ( (3 / 4) * x + 1 / x ) - Real.sqrt 3 = ( (3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1 ) / x := by
          field_simp
          <;> ring_nf <;> field_simp 
          <;> ring 
        rw [h5] 
        have h6 : (3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1 ≥ 0 := by
          nlinarith [sq_nonneg (x - 2 * Real.sqrt 3 / 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        have hx2_pos : (0 : ℝ) < x := by positivity 
        have : ( (3 / 4) * x ^ 2 - Real.sqrt 3 * x + 1 ) / x ≥ 0 := by
          apply div_nonneg 
          linarith 
          linarith 
        linarith 
      linarith 
      all_goals linarith 
    linarith [Real.sqrt_nonneg 3]