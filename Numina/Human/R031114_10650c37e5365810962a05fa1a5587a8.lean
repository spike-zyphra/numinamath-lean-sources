import Mathlib

open Real

/-If $5(\cos a + \cos b) + 4(\cos a \cos b + 1) = 0,$ then find all possible values of
\[\tan \frac{a}{2} \tan \frac{b}{2}.\]Enter all the possible values, separated by commas.-/
theorem calculus_17066 {a b : ℝ} (h : 5 * (cos a + cos b) + 4 * (cos a * cos b + 1) = 0)
(ha: cos (a / 2) ≠ 0)(hb : cos (b / 2) ≠ 0):
tan (a / 2) * tan (b / 2) = 3 ∨ tan (a / 2) * tan (b / 2) = -3 := by
-- Prove the following auxillary trigonometic identity
  have aux : ∀ x, cos (x / 2) ≠ 0 → cos x = (1 - (tan (x / 2)) ^ 2) / (1 + (tan (x / 2)) ^ 2) := by
    intro x hx; rw [Real.tan_eq_sin_div_cos, div_pow]
    field_simp; rw [Real.cos_sq, Real.sin_sq_eq_half_sub]; ring_nf
-- Rewrite the assumption h and simplify
  repeat rw [aux] at h
  apply_fun (fun x => (1 + (tan (a / 2)) ^ 2) * (1 + (tan (b / 2)) ^ 2) * x) at h
  field_simp at h; ring_nf at h
-- Solve for $tan (a / 2) * tan (b / 2)$
  apply_fun (fun x => (18 - x) / 2) at h; ring_nf at h
  rw [← mul_pow, show (9:ℝ)=3^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at h
  repeat rw [mul_div, mul_one] at h
  any_goals assumption