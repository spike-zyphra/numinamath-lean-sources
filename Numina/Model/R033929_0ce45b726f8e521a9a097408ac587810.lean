import Mathlib

theorem algebra_134161 (f : ℝ → ℝ) (hf : f = fun x => Real.sqrt ((15 * x ^ 2 + 2) / (3 * x ^ 2 + 5))) :
    ∀ x, ∃ n : ℤ, f x = n ↔ x = 1 / 2 := by
  intro x
  by_cases h : x = 1 / 2
  · -- Case x = 1/2
    use 1
    rw [h]
    have h1 : f (1 / 2 : ℝ) = (1 : ℝ) := by
      rw [hf]
      have h1 : Real.sqrt ((15 * (1 / 2 : ℝ) ^ 2 + 2) / (3 * (1 / 2 : ℝ) ^ 2 + 5)) = (1 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> norm_num
      simpa using h1
    simp [h1]
    <;> norm_num
    <;> linarith
  · -- Case x ≠ 1/2
    use 0
    have h2 : x ≠ 1 / 2 := h
    have hfx : ∀ x, f x = Real.sqrt ((15 * x ^ 2 + 2) / (3 * x ^ 2 + 5)) := by
      intro x
      rw [hf]
    have hfx2 : f x = Real.sqrt ((15 * x ^ 2 + 2) / (3 * x ^ 2 + 5)) := by
      apply hfx
    have h3 : (Real.sqrt ((15 * x ^ 2 + 2) / (3 * x ^ 2 + 5)) : ℝ) ≠ (0 : ℝ) := by
      have h4 : Real.sqrt ((15 * x ^ 2 + 2) / (3 * x ^ 2 + 5)) > 0 := by
        apply Real.sqrt_pos.2
        have h5 : (15 * x ^ 2 + 2) / (3 * x ^ 2 + 5) > 0 := by
          apply div_pos
          · -- Show numerator > 0
            nlinarith [sq_nonneg x]
          · -- Show denominator > 0
            nlinarith [sq_nonneg x]
        linarith
      linarith
    simp [hfx2, h3, h2]
    <;> norm_num [h3, h2]
    <;> tauto