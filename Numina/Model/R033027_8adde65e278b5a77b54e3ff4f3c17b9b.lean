import Mathlib
theorem algebra_611353 : IsGreatest {a : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a = x * y * z ∧ x * y + z = (x + z) * (y + z)} (1 / 27):= by 
  constructor
  · -- Show 1/27 is in the set
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Show for all a in the set, a ≤ 1/27
    intro a ha
    rcases ha with ⟨x, y, z, hx, hy, hz, ha, heq⟩
    have h1 : x + y + z = 1 := by
      nlinarith [heq, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
              h1, ha, mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)]