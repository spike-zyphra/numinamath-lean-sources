import Mathlib

theorem algebra_96938 (a b c d x y : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 0 < x ∧ 0 < y) :
    Real.log (a / b) + Real.log (b / c) + Real.log (c / d) - Real.log (a * y / (d * x)) =
    Real.log (x / y) := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  rcases h₁ with ⟨hx, hy⟩
  have h2 : Real.log (a / b) = Real.log a - Real.log b := by
    rw [Real.log_div (by linarith) (by linarith)]
  have h3 : Real.log (b / c) = Real.log b - Real.log c := by
    rw [Real.log_div (by linarith) (by linarith)]
  have h4 : Real.log (c / d) = Real.log c - Real.log d := by
    rw [Real.log_div (by linarith) (by linarith)]
  have h5 : Real.log (a * y / (d * x)) = Real.log (a * y) - Real.log (d * x) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have h6 : Real.log (a * y) = Real.log a + Real.log y := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h7 : Real.log (d * x) = Real.log d + Real.log x := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h8 : Real.log (x / y) = Real.log x - Real.log y := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [h2, h3, h4, h5, h6, h7, h8]
  ring