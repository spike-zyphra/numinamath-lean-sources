import Mathlib

theorem algebra_159342 (n : ℕ) (hn : n = 100) (r : ℝ) (hr : r = 0.2) :
    r * √(n - 2) / √(1 - r ^ 2) > 1.99 := by
  rw [hn, hr]
  have h1 : (0.2 : ℝ) * √(100 - 2) / √(1 - (0.2 : ℝ) ^ 2) > 1.99 := by
    have h2 : √(98 : ℝ) > 9.8 := by
      have h2 : (9.8 : ℝ) ^ 2 < (98 : ℝ) := by norm_num
      have h3 : √((98 : ℝ)) > √((9.8 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
      have h4 : √((9.8 : ℝ) ^ 2) = (9.8 : ℝ) := Real.sqrt_sq (by norm_num)
      linarith [h3, h4]
    have h3 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) < (0.98 : ℝ) := by
      have h4 : (1 - (0.2 : ℝ) ^ 2 : ℝ) < (0.98 : ℝ) ^ 2 := by norm_num
      have h5 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) < √((0.98 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      have h6 : √((0.98 : ℝ) ^ 2) = (0.98 : ℝ) := Real.sqrt_sq (by norm_num)
      linarith [h5, h6]
    have h4 : (0.2 : ℝ) * √(98) / √(1 - (0.2 : ℝ) ^ 2) > (0.2 : ℝ) * (9.8 : ℝ) / (0.98 : ℝ) := by
      have h5 : √(98 : ℝ) > (9.8 : ℝ) := by
        have h6 : (9.8 : ℝ) ^ 2 < (98 : ℝ) := by norm_num
        have h7 : √((98 : ℝ)) > √((9.8 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
        have h8 : √((9.8 : ℝ) ^ 2) = (9.8 : ℝ) := Real.sqrt_sq (by norm_num)
        linarith [h7, h8]
      have h6 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) < (0.98 : ℝ) := by
        have h7 : (1 - (0.2 : ℝ) ^ 2 : ℝ) < (0.98 : ℝ) ^ 2 := by norm_num
        have h8 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) < √((0.98 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
        have h9 : √((0.98 : ℝ) ^ 2) = (0.98 : ℝ) := Real.sqrt_sq (by norm_num)
        linarith [h8, h9]
      have h7 : (0.2 : ℝ) * √(98 : ℝ) / √((1 - (0.2 : ℝ) ^ 2) : ℝ) > (0.2 : ℝ) * (9.8 : ℝ) / (0.98 : ℝ) := by
        have h8 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) > 0 := by
          apply Real.sqrt_pos.2
          norm_num
        have h9 : √(98 : ℝ) > 0 := by
          apply Real.sqrt_pos.2
          norm_num
        have h10 : (0.2 : ℝ) * √(98 : ℝ) / √((1 - (0.2 : ℝ) ^ 2) : ℝ) - (0.2 : ℝ) * (9.8 : ℝ) / (0.98 : ℝ) > 0 := by
          have h11 : √(98 : ℝ) * (0.98 : ℝ) - (9.8 : ℝ) * √((1 - (0.2 : ℝ) ^ 2) : ℝ) > 0 := by
            nlinarith [h5, h6, Real.sqrt_nonneg ((1 - (0.2 : ℝ) ^ 2) : ℝ)]
          have h12 : (0.2 : ℝ) * √(98 : ℝ) / √((1 - (0.2 : ℝ) ^ 2) : ℝ) - (0.2 : ℝ) * (9.8 : ℝ) / (0.98 : ℝ) =
              (0.2 : ℝ) * (√(98 : ℝ) * (0.98 : ℝ) - (9.8 : ℝ) * √((1 - (0.2 : ℝ) ^ 2) : ℝ)) / (√((1 - (0.2 : ℝ) ^ 2) : ℝ) * (0.98 : ℝ)) := by
            field_simp
            ring
          rw [h12]
          have h13 : √((1 - (0.2 : ℝ) ^ 2) : ℝ) * (0.98 : ℝ) > 0 := by
            apply mul_pos
            · apply Real.sqrt_pos.2
              norm_num
            · norm_num
          apply div_pos
          · nlinarith [h11]
          · nlinarith [h13]
        nlinarith [h10]
      linarith [h7]
    have h5 : (0.2 : ℝ) * (9.8 : ℝ) / (0.98 : ℝ) = 2 := by norm_num
    linarith [h4, h5]
  linarith [h1]