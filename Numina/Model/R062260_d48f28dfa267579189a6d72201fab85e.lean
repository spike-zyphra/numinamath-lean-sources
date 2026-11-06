import Mathlib

theorem algebra_6060 (v1 : ℝ) (h : v1 > 0) (h' : 335 / v1 = 330 / (v1 + 1188)) :
    v1 < 67 * v1 - 330 / 66 := by
  have eq1 : v1 * (v1 + 1188) ≠ 0 := by
    apply mul_ne_zero
    · -- v1 ≠ 0
      linarith
    · -- v1 + 1188 ≠ 0
      by_contra h1
      nlinarith
  field_simp [show v1 ≠ 0 by linarith, show v1 + 1188 ≠ 0 by
     by_contra h1
     nlinarith
  ] at h'
  nlinarith