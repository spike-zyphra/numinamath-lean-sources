import Mathlib

open Real

/- 90 Given $\sin x+\sin y=\log _{2} 2, \cos x+\cos y=\log _{7} 4$, then the value of $\cos 2(x+y)$ is
 -/
theorem algebra_144153 (x y : ℝ) (h₁ : sin x + sin y = logb 7 2)
    (h₂ : cos x + cos y = logb 7 4) :
    cos (2 * (x + y)) = -7 / 25 := by
  -- write the sums as product of sin/cos
  nth_rw 1 [show y = (x + y) / 2 + (y - x) / 2 by ring] at h₁
  nth_rw 1 [show x = (x + y) / 2 - (y - x)/2 by ring] at h₁
  rw [← two_mul_sin_mul_cos, ← cos_neg, show -((y-x)/2) = (x-y)/2 by ring] at h₁
  rw [cos_add_cos] at h₂
  -- sin (x + y)/2, cos (x + y)/2, cos (x - y)/2 are not 0 as logs are not 0
  have : sin ((x + y)/2) ≠ 0 := by
    by_contra h
    rw [h, eq_comm] at h₁
    simp at h₁
    norm_num at h₁
  have : cos ((x + y)/2) ≠ 0 := by
    by_contra h
    rw [h, eq_comm] at h₂
    simp at h₂
    norm_num at h₂
  have : cos ((x - y)/2) ≠ 0 := by
    by_contra h
    rw [h, eq_comm] at h₁
    simp at h₁
    norm_num at h₁
  -- divide the equations, getting tan
  have h₃ : (2 * sin ((x + y) / 2) * cos ((x - y) / 2)) / (2 * cos ((x + y) / 2) * cos ((x - y) / 2)) = (logb 7 2) / (logb 7 4) := by rw [h₁, h₂]
  convert_to tan ((x + y)/2) = log 2 / log 4 at h₃
  . rw [tan_eq_sin_div_cos]
    field_simp
    ring
  . rw [logb, logb]
    field_simp
  -- show the rhs is 1/2 in the tan equation
  rw [show (4 : ℝ) = 2^2 by norm_num] at h₃
  simp at h₃
  rw [show log 2 / (2 * log 2) = 1 / 2 by field_simp; ring] at h₃
  -- now write cos (2 * (x + y)) in terms of tan and plug in
  have aux (θ : ℝ) (h : cos θ ≠ 0) : cos (2 * θ) = (1 - tan θ ^ 2) / (1 + tan θ ^ 2) := by
    rw [show cos (2 * θ) = cos (2 * θ) / 1 by ring, cos_two_mul']
    nth_rw 1 [← sin_sq_add_cos_sq θ]
    rw [tan_eq_sin_div_cos]
    field_simp
  specialize aux ((x + y)/2) (by assumption)
  rw [h₃] at aux
  ring_nf at aux
  rw [cos_two_mul, aux]
  norm_num