import Mathlib

open Real

theorem algebra_306918 (f : ℝ → ℝ) (hf : f = fun x => (10 / (10 ^ x + 1)) - 3) :
    ∀ x, f x ∈ Set.Ioo (-3) 7 := by
  intro x
  rw [hf]
  simp only [Set.mem_Ioo]
  constructor
  · -- Prove -3 < (10 / (10 ^ x + 1) - 3)
    have hx1 : (10 / (10 ^ x + 1 : ℝ) : ℝ) > 0 := by
      apply div_pos
      norm_num
      -- Show denominator is positive: 10 ^ x > 0 so 10 ^ x + 1 > 0
      have h1 : (10 : ℝ) ^ x > 0 := Real.rpow_pos_of_pos (by norm_num) x
      linarith [show (10 : ℝ) ^ x + 1 > 0 by linarith]
    linarith [hx1]
  · -- Prove (10 / (10 ^ x + 1) - 3) < 7
    have hx2 : (10 / (10 ^ x + 1 : ℝ) : ℝ) < 10 := by
      have h1 : (10 : ℝ) ^ x > 0 := Real.rpow_pos_of_pos (by norm_num) x
      have h2 : (10 : ℝ) ^ x + 1 > 0 := by linarith
      -- Show that 10 / (10 ^ x + 1) < 10 by multiplying both sides by denominator
      have h3 : (10 : ℝ) / (10 ^ x + 1) < 10 := by
        have h4 : 0 < (10 ^ x + 1 : ℝ) := by linarith
        apply (div_lt_iff (by linarith)).mpr
        -- Show that 10 < 10 * (10 ^ x + 1)
        nlinarith [Real.rpow_pos_of_pos (by norm_num : (10 : ℝ) > 0) x]
      linarith [h3]
    linarith [hx2]