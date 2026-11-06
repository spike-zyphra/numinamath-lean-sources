import Mathlib

theorem algebra_128834 (x : ℝ) (h : Real.sin (Real.pi / 4 - x) = 3 / 5) : Real.sin (2 * x) = 7 / 25 := by
  have h1 : Real.sin (Real.pi / 4 - x) = 3 / 5 := h
  -- let θ := Real.pi / 4 - x
  let θ := Real.pi / 4 - x
  have h2 : Real.sin θ = 3 / 5 := h
  -- x = Real.pi / 4 - θ
  have hx : x = Real.pi / 4 - θ := by ring_nf
  -- 2 * x = Real.pi / 2 - 2 * θ
  have h2x : 2 * x = Real.pi / 2 - 2 * θ := by 
    rw [hx]
    ring
  rw [h2x]
  have h3 : Real.sin (Real.pi / 2 - 2 * θ) = Real.cos (2 * θ) := by
    rw [Real.sin_pi_div_two_sub]
  rw [h3]
  -- compute cos(2θ) using double angle formula and sin^2θ + cos^2θ = 1
  have h4 : Real.cos (2 * θ) = 1 - 2 * (Real.sin θ)^2 := by
    rw [Real.cos_two_mul, Real.sin_sq]
    ring_nf
    <;> nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h4, h2]
  norm_num