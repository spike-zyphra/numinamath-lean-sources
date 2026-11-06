import Mathlib

open EuclideanGeometry
open Real

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/- The legs of a right triangle have lengths $\log_4 27$ and $\log_2 9.$ If the length of the hypotenuse is $h,$ compute $4^h.$ -/
theorem algebra_12308 {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (ha : dist p₁ p₂ = Real.logb 4 27) (hb : dist p₃ p₂ = Real.logb 2 9) : (4 : ℝ) ^ (dist p₁ p₃) = 243 := by
  -- we apply Pythagorean Theorem, we get $c^2 = log_{4}27 + log_{2}9$
  rw [← EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two] at h

  -- proof of $log_{2}9 = 4log_{4}3$
  have hlog29 : Real.logb 2 9 = 4 * Real.logb 4 3 := by
    have hinner : Real.logb 2 9 = logb 2 4 * logb 4 9 := by
      rw [← mul_logb (show 4 ≠ 0 by simp)]
      simp
      linarith
    rw [hinner]
    conv =>
      lhs
      lhs
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by ring_nf]
    rw [logb_rpow_eq_mul_logb_of_pos]
    rw [logb_self_eq_one]
    ring_nf
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by ring_nf]
    rw [logb_rpow_eq_mul_logb_of_pos]
    ring_nf
    repeat simp

  -- proof of $c^2 = 25 * log_{4}3 * log_{4}3$
  have heq := calc
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ := h
    _ = (Real.logb 4 27) * (Real.logb 4 27) + (Real.logb 2 9) * (Real.logb 2 9) := by rw [ha, hb]
    _ = (Real.logb 4 (3 ^ (3 : ℝ))) * (Real.logb 4 (3 ^ (3 : ℝ))) + (Real.logb 2 9) * (Real.logb 2 9) := by ring_nf
    _ = (3 * (Real.logb 4 3)) * (3 * (Real.logb 4 3)) + (Real.logb 2 9) * (Real.logb 2 9) := by rw [logb_rpow_eq_mul_logb_of_pos]; simp
    _ = (3 * (Real.logb 4 3)) * (3 * (Real.logb 4 3)) + (4 * (Real.logb 4 3)) *  (4 * (Real.logb 4 3)) := by rw [hlog29]
    _ = 25 * (Real.logb 4 3) * (Real.logb 4 3) := by ring_nf

  apply_fun (√.) at heq
  rw [← pow_two, sqrt_sq] at heq
  replace heq := calc
    dist p₁ p₃ = √(25 * logb 4 3 * logb 4 3) := heq
    _ = √(25 * (logb 4 3 * logb 4 3)) := by ring_nf
    _ = 5 * (Real.logb 4 3) := by
      rw [sqrt_mul]
      rw [show (25 : ℝ) = 5 ^ 2 by ring_nf]
      rw [←pow_two]
      repeat rw [sqrt_sq]
      have logb43lt0 : 0 < logb 4 3 := by
        rw [logb_pos_iff]
        repeat simp
      linarith
      repeat simp

  -- $c^2 = 25 * log_{4}3 * log_{4}3$ → $c = 5 * log_{4}3$
  rw [heq]
  rw [← logb_rpow_eq_mul_logb_of_pos]
  rw [rpow_logb]
  ring_nf
  repeat simp
  ring_nf; repeat simp
  apply dist_nonneg
