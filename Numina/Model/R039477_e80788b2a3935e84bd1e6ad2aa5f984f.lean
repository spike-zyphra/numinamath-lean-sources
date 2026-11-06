import Mathlib

theorem algebra_22020 {f g : ℝ → ℝ} (hf : f = Real.sqrt) (hg : g = fun x => x ^ 2) :
    f (g (f (g (f 8)))) = 2 * Real.sqrt 2 := by
  have h1 : f 8 = Real.sqrt 8 := by
    simp [hf]
  have h2 : g (f 8) = 8 := by
    rw [h1]
    rw [hg]
    have h7 : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    simpa using h7
  have h3 : f (g (f 8)) = Real.sqrt 8 := by
    rw [h2]
    simp [hf]
  have h4 : g (f (g (f 8))) = 8 := by
    rw [h3]
    rw [hg]
    have h7 : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    simpa using h7
  have h5 : f (g (f (g (f 8)))) = Real.sqrt 8 := by
    rw [h4]
    simp [hf]
  have h6 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 8 = Real.sqrt (2 ^ 2 * 2) := by norm_num
      _ = (Real.sqrt (2 ^ 2)) * (Real.sqrt (2)) := by rw [Real.sqrt_mul (by norm_num)]
      _ = (2) * (Real.sqrt 2) := by
        rw [Real.sqrt_sq (by norm_num)]
      _ = 2 * Real.sqrt 2 := by ring
  rw [h5, h6]