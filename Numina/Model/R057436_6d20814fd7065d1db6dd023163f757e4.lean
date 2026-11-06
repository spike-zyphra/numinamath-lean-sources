import Mathlib

theorem algebra_228797 {x : ℝ} (hx : x = (1 + Real.sqrt 1994) / 2) :
    (4 * x ^ 3 - 1997 * x - 1994) ^ 20001 = -1 := by
  have h1 : x = (1 + Real.sqrt 1994) / 2 := hx 
  have h2 : x - 1 / 2 = Real.sqrt 1994 / 2 := by 
    rw [h1]
    ring_nf
  have h3 : (x - 1 / 2) ^ 2 = (Real.sqrt 1994) ^ 2 / 4 := by 
    rw [h2]
    <;> ring_nf <;> simp [Real.sq_sqrt] <;> linarith
  have h4 : (x - 1 / 2) ^ 2 = x^2 - x + (1/4 : ℝ) := by 
    ring_nf
  rw [h4] at h3 
  have h5 : x^2 - x + (1/4 : ℝ) = (Real.sqrt 1994) ^ 2 / 4 := by 
    linarith 
  have h6 : (Real.sqrt 1994) ^ 2 = 1994 := Real.sq_sqrt (show (0 : ℝ) ≤ 1994 by norm_num)
  rw [h6] at h5 
  have h7 : 4 * x^2 - 4 * x - 1993 = 0 := by 
    nlinarith 
  have eq1 : x^2 = x + (1993 / 4 : ℝ) := by 
    nlinarith 
  have eq2 : x^3 = (1997 / 4 : ℝ) * x + (1993 / 4 : ℝ) := by 
    calc 
      x^3 = x * x^2 := by ring
      _ = x * (x + 1993 / 4) := by rw [eq1]
      _ = x^2 + (1993 / 4) * x := by ring
      _ = (x + 1993 / 4) + (1993 / 4) * x := by rw [eq1]
      _ = (1997 / 4) * x + (1993 / 4) := by ring
  have eq3 : 4 * x^3 = 1997 * x + 1993 := by 
    linarith [eq2]
  have eq4 : 4 * x^3 - 1997 * x - 1994 = -1 := by 
    linarith [eq3]
  rw [eq4]
  norm_num