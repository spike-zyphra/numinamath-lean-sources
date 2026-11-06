import Mathlib

theorem algebra_21510 (d : ℝ) (h : d > 0) (P F1 F2 : ℝ × ℝ)
    (hP : P = (0, 0)) (hF1 : F1 = (-7, 0)) (hF2 : F2 = (7, 0))
    (hP1 : d = Real.sqrt ((P.1 - F1.1)^2 + (P.2 - F1.2)^2) +
      Real.sqrt ((P.1 - F2.1)^2 + (P.2 - F2.2)^2)) :
    d = 14 := by
  rw [hP, hF1, hF2] at hP1
  have h1 : Real.sqrt (( (0 : ℝ ) - (-7 : ℝ) ) ^ 2 + ( (0 : ℝ) - (0 : ℝ) ) ^ 2 ) = 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> nlinarith
  have h2 : Real.sqrt (( (0 : ℝ ) - (7 : ℝ) ) ^ 2 + ( (0 : ℝ) - (0 : ℝ) ) ^ 2 ) = 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> nlinarith
  rw [h1, h2] at hP1
  linarith