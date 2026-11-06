import Mathlib

/- The first three terms of a geometric progression are sqrt(3), sqrt[3](3), sqrt[6](3). What is the fourth term?
(A) 1
(B) sqrt[7](3)
(C) sqrt[8](3)
(D) sqrt[9](3)
(E) sqrt[10](3)

  -/
theorem algebra_96192 (a r : ℝ) (h₀ : a = Real.sqrt 3) (h₁ : r ≠ 0)
(h₂ : a * r = 3 ^ ((1 : ℝ) / 3)) (h₃ : a * r * r = 3 ^ ((1 : ℝ) / 6)) :
a * r * r * r = 1 := by
  -- prove 0 < a for use in division
  have : 0 < a := by
    rw [h₀]
    norm_num
  -- now prove r = 3^(-1/6) by ar / a
  rw [h₀] at h₂
  have hr: r = (3:ℝ)^(-(1:ℝ)/6) := by
    calc
      r = a * r / a := by field_simp
      _ = 3^((1:ℝ)/3) / √3 := by rw [← h₂, h₀]
      _ = 3^((1:ℝ)/3) / 3^((1:ℝ)/2) := by
        congr
        exact Real.sqrt_eq_rpow 3
      _ = 3 ^ ((1:ℝ)/3 - (1:ℝ)/2) := by
        refine Eq.symm (Real.rpow_sub ?_ _ _)
        norm_num
      _ = (3:ℝ)^(-(1:ℝ)/6) := by norm_num
  -- plug in values and calculate
  rw [h₃, hr, ← Real.rpow_add]
  repeat norm_num