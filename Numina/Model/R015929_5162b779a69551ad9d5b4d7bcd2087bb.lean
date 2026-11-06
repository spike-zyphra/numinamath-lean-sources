import Mathlib

open Real

theorem algebra_327104 {f : ℝ → ℝ} (hf : ∀ x, x ≠ -abs x → f (2 / (x + abs x)) = logb 2 (sqrt (x * abs x))) :
    ∀ x, x ≠ -abs x → f x = -logb 2 x := by
  intro x hx
  have h1 : x > 0 := by
    by_contra h
    push_neg at h
    by_cases h2 : x < 0
    · -- Case where x < 0.
      have h3 : abs x = -x := by
        rw [abs_of_neg h2]
      have h4 : -abs x = x := by
        have h5 : abs x = -x := h3
        linarith [h5]
      have h5 : x = -abs x := by linarith [h4]
      have h6 : x ≠ -abs x := hx
      contradiction
    · -- Case where x ≥ 0.
      have h7 : x = 0 := by
        linarith [show x ≥ 0 from by linarith, show x ≤ 0 from by linarith]
      rw [h7] at hx
      norm_num [abs_zero] at hx
  have h2 : f x = -logb 2 x := by
    have h3 : f (2 / ((1 / x) + abs (1 / x))) = logb 2 (sqrt ((1 / x) * abs (1 / x))) := by
      apply hf (1 / x)
      -- Show that 1/x ≠ -abs (1/x) when x > 0
      have hx11 : 1 / x > 0 := by
        apply div_pos
        norm_num
        linarith
      have h55 : abs (1 / x) = (1 / x) := by
        rw [abs_of_pos hx11]
      have h66 : (1 / x) ≠ -abs (1 / x) := by
        rw [h55]
        intro h
        have h77 : (1 / x) = 0 := by linarith
        have h88 : (1 / x) > 0 := hx11
        linarith
      exact h66
    have h44 : (1 / x) + abs (1 / x) = 2 / x := by
      have hx11 : 1 / x > 0 := by
        apply div_pos
        norm_num
        linarith
      have h55 : abs (1 / x) = (1 / x) := by
        rw [abs_of_pos hx11]
      rw [h55]
      field_simp
      <;> ring
    have h77 : 2 / ((1 / x) + abs (1 / x)) = x := by
      rw [h44]
      field_simp
      <;> nlinarith
    have h88 : (1 / x) * abs (1 / x) = (1 / x) * (1 / x) := by
      have hx11 : 1 / x > 0 := by
        apply div_pos
        norm_num
        linarith
      have h55 : abs (1 / x) = (1 / x) := by
        rw [abs_of_pos hx11]
      rw [h55]
    have h99 : sqrt ((1 / x) * abs (1 / x)) = 1 / x := by
      rw [h88]
      have h100 : (1 / x) * (1 / x) = (1 / x) ^ 2 := by ring
      rw [h100]
      have h111 : sqrt ((1 / x) ^ 2) = (1 / x) := by
        rw [Real.sqrt_sq]
        have h120 : 1 / x ≥ 0 := by
          apply div_nonneg
          norm_num
          linarith
        linarith
      linarith
    rw [h77] at h3
    rw [h99] at h3
    have h111 : logb 2 (1 / x) = -logb 2 x := by
      have h111 : logb 2 (1 / x) = logb 2 1 - logb 2 x := by
        field_simp [logb_div]
      have h112 : logb 2 1 = 0 := by
        simp [logb_one]
      rw [h111, h112]
      all_goals linarith
    linarith [h3, h111]
  exact h2