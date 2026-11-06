import Mathlib

theorem algebra_306166 {f : ℝ → ℝ}
    (hf : ∀ x, f x = x ^ 10 + 2 * x ^ 9 - 2 * x ^ 8 - 2 * x ^ 7 + x ^ 6 + 3 * x ^ 2 + 6 * x + 1) :
    f (Real.sqrt 2 - 1) = 4 := by
  rw [hf]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := h2
  have h4 : (Real.sqrt 2 : ℝ) ^ 3 = (Real.sqrt 2 : ℝ) * 2 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 3 = (Real.sqrt 2 : ℝ) ^ 2 * (Real.sqrt 2 : ℝ) := by ring
      _ = (2 : ℝ) * (Real.sqrt 2 : ℝ) := by rw [h3]
      _ = (Real.sqrt 2 : ℝ) * 2 := by ring
  have h5 : (Real.sqrt 2 : ℝ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 4 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 2 := by ring
      _ = (2 : ℝ) ^ 2 := by rw [h3]
      _ = (4 : ℝ) := by norm_num
  have h6 : (Real.sqrt 2 : ℝ) ^ 5 = (Real.sqrt 2 : ℝ) * 4 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 5 = (Real.sqrt 2 : ℝ) ^ 4 * (Real.sqrt 2 : ℝ) := by ring
      _ = (4 : ℝ) * (Real.sqrt 2 : ℝ) := by rw [h5]
      _ = (Real.sqrt 2 : ℝ) * 4 := by ring
  have h7 : (Real.sqrt 2 : ℝ) ^ 6 = 8 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 6 = (Real.sqrt 2 : ℝ) ^ 4 * (Real.sqrt 2 : ℝ) ^ 2 := by ring
      _ = (4 : ℝ) * (2 : ℝ) := by rw [h5, h3]
      _ = (8 : ℝ) := by norm_num
  have h8 : (Real.sqrt 2 : ℝ) ^ 7 = (Real.sqrt 2 : ℝ) * 8 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 7 = (Real.sqrt 2 : ℝ) ^ 6 * (Real.sqrt 2 : ℝ) := by ring
      _ = (8 : ℝ) * (Real.sqrt 2 : ℝ) := by rw [h7]
      _ = (Real.sqrt 2 : ℝ) * 8 := by ring
  have h9 : (Real.sqrt 2 : ℝ) ^ 8 = 16 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 8 = (Real.sqrt 2 : ℝ) ^ 4 * (Real.sqrt 2 : ℝ) ^ 4 := by ring
      _ = (4 : ℝ) * (4 : ℝ) := by rw [h5]
      _ = (16 : ℝ) := by norm_num
  have h10 : (Real.sqrt 2 : ℝ) ^ 9 = (Real.sqrt 2 : ℝ) * 16 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 9 = (Real.sqrt 2 : ℝ) ^ 8 * (Real.sqrt 2 : ℝ) := by ring
      _ = (16 : ℝ) * (Real.sqrt 2 : ℝ) := by rw [h9]
      _ = (Real.sqrt 2 : ℝ) * 16 := by ring
  have h11 : (Real.sqrt 2 : ℝ) ^ 10 = 32 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 10 = (Real.sqrt 2 : ℝ) ^ 6 * (Real.sqrt 2 : ℝ) ^ 4 := by ring
      _ = (8 : ℝ) * (4 : ℝ) := by rw [h7, h5]
      _ = (32 : ℝ) := by norm_num
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
    Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
    sq_nonneg ((Real.sqrt 2 - 1) : ℝ)]