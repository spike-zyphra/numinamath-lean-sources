import Mathlib

theorem algebra_2473 :
  IsGreatest {6 * (y + z - x) + 27 * x * y * z | (x : ℝ) (y : ℝ) (z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1)} 10 := by 
  constructor
  · -- Show 10 is achievable
    use 1 / 3, 2 / 3, 2 / 3
    norm_num
  · -- Show no greater value is achievable
    intro p hp
    rcases hp with ⟨x, y, z, hx, hy, hz, h, hp⟩
    have h1 : 6 * (y + z - x) + 27 * x * y * z ≤ 10 := by
      have h2 : 0 ≤ z := hz
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz,
          sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (z - 2 / 3)]
    linarith
  all_goals linarith