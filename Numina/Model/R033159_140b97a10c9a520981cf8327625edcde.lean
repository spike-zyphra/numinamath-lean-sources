import Mathlib

theorem number_theory_114397 : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  rw [Irrational]
  simp only [Set.mem_range]
  rintro ⟨q, hq⟩
  have hx : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Rat.cast q) ^ 2 := by
    rw [hq]
  -- Calculation proof that (sqrt2 + sqrt3)^2 = 5 + 2 * sqrt6
  have hx_expanded : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * Real.sqrt 6 := by
    calc
      (Real.sqrt 2 + Real.sqrt 3) ^ 2 = Real.sqrt 2 ^ 2 + Real.sqrt 3 ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring
      _ = 2 + 3 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by
        have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
        have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
        nlinarith [h2, h3]
      _ = 5 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring_nf
      _ = 5 + 2 * Real.sqrt (2 * 3) := by
        have h4 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by
          rw [← Real.sqrt_mul (by norm_num)]
        rw [h4]
      _ = 5 + 2 * Real.sqrt 6 := by norm_num
  -- Now equate both expressions
  have h_eq : (5 + 2 * Real.sqrt 6) = (Rat.cast q ^ 2) := by
    nlinarith [hx, hx_expanded]
  have h4 : (Real.sqrt 6) = (Rat.cast q ^ 2 - 5) / (2 : ℝ) := by
    nlinarith
  have h6 : Irrational (Real.sqrt 6) := by
    native_decide
  -- So, this says sqrt6 is rational, which is false
  have h7 : ¬ Irrational (Real.sqrt 6) := by
    simp [Irrational] at *
    use (q ^ 2 - 5) / (2 : ℚ)
    norm_num at h4 ⊢
    all_goals try { tauto }
    all_goals try { nlinarith [h4] }
  exfalso
  contradiction