import Mathlib

theorem algebra_305444 (a b : ℝ) (h₀ : a + 3 * b ≠ 0) (h₁ : 7 * a - 5 * b ≠ 0)
    (h₂ : a - 4 * b ≠ 0) (h₃ : 7 * a - 2 ≠ 0) (h₄ : (a + 3 * b) * (7 * a - 5 * b) = 0)
    (h₅ : (a - 4 * b) * (7 * a - 2) = 0) :
    Real.arccos ((a * b) / (Real.sqrt (a ^ 2 + b ^ 2))) = Real.pi / 3 := by
  have h6 : a - 4 * b = 0 := by
    apply (mul_left_inj' h₃).mp
    linarith
  have ha : a = 4 * b := by linarith
  have h7 : b = 0 := by
    rw [show a = 4 * b by linarith [ha]] at h₄ 
    nlinarith
  have h8 : a = 0 := by
    linarith [ha, h7]
  have h9 : a + 3 * b = 0 := by
    linarith [h8, h7]
  contradiction