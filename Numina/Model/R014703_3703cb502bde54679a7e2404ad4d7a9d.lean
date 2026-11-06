import Mathlib

theorem algebra_952 {a b x y : ℝ} (h₁ : a * x + b * y = 7) (h₂ : a * x^2 + b * y^2 = 49) (h₃ : a * x^3 + b * y^3 = 133) (h₄ : a * x^4 + b * y^4 = 406) :
    1995 * (x + y) + 6 * x * y - 17 / 2 * (a + b) = 4800 := by

  have h₅ : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - x * y * (a * x + b * y) := by
    ring
  rw [h₁, h₂, h₃] at h₅
  have eq1 : x * y = 7 * (x + y) - 19 := by 
    nlinarith
  have h₆ : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - x * y * (a * x^2 + b * y^2) := by
    ring
  rw [h₂, h₃, h₄] at h₆
  have h₇ : x + y = 5 / 2 := by
    have eq1' : x * y = 7 * (x + y) - 19 := eq1
    nlinarith [sq_nonneg (x + y - 5 / 2), sq_nonneg (x - y), sq_nonneg (a * x - b * y)]
  have h₈ : x * y = -3 / 2 := by
    rw [h₇] at eq1
    nlinarith
  have h₉ : a + b = 21 := by
    have eq2 : a * x^2 + b * y^2 = (x + y) * (a * x + b * y) - x * y * (a + b) := by 
      ring
    rw [h₁, h₂, h₇, h₈] at eq2
    nlinarith
  -- Now the final part of the proof
  -- instead of mucking with subs we have proven so far
  have eq2 : 1995 * (x + y) + 6 * x * y - 17 / 2 * (a + b) = 4800 := by
    have eq3 : x + y = 5 / 2 := h₇
    have eq4 : x * y = -3 / 2 := h₈
    have eq5 : a + b = 21 := h₉
    have eq6 : 1995 * (x + y) = 1995 * (5 / 2) := by
      rw [eq3]
    have eq7 : 6 * x * y = 6 * (-3 / 2) := by 
      have eq8 : x * y = -3 / 2 := h₈ 
      have eq9 : 6 * x * y = 6 * (x * y) := by ring
      rw [eq9, eq8]
    have eq8 : 17 / 2 * (a + b) = 17 / 2 * (21) := by 
      rw [eq5]
    linarith [eq6, eq7, eq8]

  linarith [eq2]