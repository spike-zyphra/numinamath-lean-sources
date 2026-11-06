import Mathlib

theorem algebra_9072 (f : ℝ → ℝ) (hf : f = Real.sin) : deriv f (Real.pi / 2) = 0 := by
  rw [hf]
  have h1 : deriv Real.sin (Real.pi / 2) = Real.cos (Real.pi / 2) := by
    simp [Real.deriv_sin]
  rw [h1]
  exact Real.cos_pi_div_two