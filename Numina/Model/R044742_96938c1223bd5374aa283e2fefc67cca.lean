import Mathlib

theorem algebra_191507 {f : ℝ → ℝ} (hf : f = fun x => x^8 + x^4 + 1) :
    f = (fun x => (x^2 - Real.sqrt 3 * x + 1) * (x^2 + Real.sqrt 3 * x + 1) *
      (x^2 - x + 1) * (x^2 + x + 1)) := by
  funext x
  rw [hf]
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have h2 : (x ^ 2 - Real.sqrt 3 * x + 1) * (x ^ 2 + Real.sqrt 3 * x + 1) =
      x^4 - x^2 + 1 := by 
    nlinarith [h1, sq_nonneg (x * Real.sqrt 3), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - Real.sqrt 3 * x), sq_nonneg (x + Real.sqrt 3 * x)]
  have h3 : (x^2 - x + 1) * (x^2 + x + 1) = x^4 + x^2 + 1 := by 
    nlinarith [sq_nonneg (x * (x + 1)), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  calc
    x^8 + x^4 + 1
      = (x^4 - x^2 + 1) * (x^4 + x^2 + 1) := by 
        ring
    _ = ((x ^ 2 - Real.sqrt 3 * x + 1) * (x ^ 2 + Real.sqrt 3 * x + 1)) * ((x^2 - x + 1) * (x^2 + x + 1)) := by 
      rw [h2, h3]
    _ = (x^2 - Real.sqrt 3 * x + 1) * (x^2 + Real.sqrt 3 * x + 1) * (x^2 - x + 1) * (x^2 + x + 1) := by 
      ring