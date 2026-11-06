import Mathlib

/- A right rectangular prism whose surface area and volume are numerically equal has edge lengths
log_{2}x, log_{3}x, and log_{4}x What is x?

(A) 26
(B) 66
(C) 24
(D) 48
(E) 576
(A) 2 -/
theorem algebra_94813 {x : ℝ} (hx : x > 0)
(h : 2 * (Real.logb 2 x * Real.logb 3 x +  Real.logb 2 x * Real.logb 4 x + Real.logb 3 x * Real.logb 4 x) = Real.logb 2 x * Real.logb 3 x * Real.logb 4 x)
(h2pos: Real.logb 2 x > 0)
(h3pos: Real.logb 3 x > 0)
(h4pos: Real.logb 4 x > 0)
: x = 576 := by

  -- divide both sides by log_{2}x log_{3}x log_{4}x
  apply congr_arg (fun f => f / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x)) at h
  -- add proof that product of logarithms > 0, is > 0
  have :0 < Real.logb 2 x * Real.logb 3 x * Real.logb 4 x := by
    refine mul_pos (mul_pos ?_ ?_) ?_
    all_goals {linarith}
  -- cancel out right side of assumption h
  rw [div_eq_mul_inv (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x ), mul_inv_cancel₀ (by linarith)] at h

  -- rewrite help_h to cancel out fractions
  have help_h :=
    calc 2 * (Real.logb 2 x * Real.logb 3 x + Real.logb 2 x * Real.logb 4 x + Real.logb 3 x * Real.logb 4 x) / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x)
    _ = 2 * ((Real.logb 2 x * Real.logb 3 x + Real.logb 2 x * Real.logb 4 x + Real.logb 3 x * Real.logb 4 x) / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x)) := by ring_nf
    _ = 2 * (Real.logb 2 x * Real.logb 3 x / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x) + (Real.logb 2 x * Real.logb 4 x) / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x) + Real.logb 3 x * Real.logb 4 x / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x)) := by ring_nf
    _ = 2 * ((Real.logb 2 x  / Real.logb 2 x * (Real.logb 3 x / Real.logb 3 x) / Real.logb 4 x) + (Real.logb 2 x / Real.logb 2 x * (Real.logb 4 x / Real.logb 4 x) / Real.logb 3 x) + (Real.logb 3 x / Real.logb 3 x * (Real.logb 4 x / Real.logb 4 x) / Real.logb 2 x)) := by ring_nf
  repeat rw [div_eq_mul_inv] at help_h
  repeat rw [mul_inv_cancel₀ (by linarith)] at help_h
  simp at help_h

  have h5:((Real.logb 4 x)⁻¹ * ((Real.logb 3 x)⁻¹ * (Real.logb 2 x)⁻¹)) =
        1 / (Real.logb 2 x * Real.logb 3 x * Real.logb 4 x) := by
    ring_nf
  rw [h5, mul_one_div] at help_h
  rw [help_h] at h
  -- swap logarithm bases
  repeat rw [Real.inv_logb] at h
  -- swap sum of logarithm into one logarithm with multiplication inside
  rw [← Real.logb_mul (by norm_num) (by norm_num), ← Real.logb_mul (by norm_num) (by norm_num)] at h; norm_num at h
  -- rewrite logarithm
  apply congr_arg (fun x=> 2⁻¹*x) at h; simp at h; rw[Real.logb_eq_iff_rpow_eq (by linarith) (by intro hx; rw [hx, Real.logb_one] at h2pos; linarith) (by norm_num)] at h
  apply congr_arg (fun x=> x^(2:ℝ)) at h
  -- cancel out powers and compare to goal
  rw [← Real.rpow_mul] at h; simp at h; linarith
  linarith