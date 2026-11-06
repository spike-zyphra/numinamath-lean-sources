import Mathlib

theorem algebra_181182 (x y z t : ℝ) :
    x^2 + y^2 + z^2 + t^2 = x * (y + z + t) ↔ (x, y, z, t) = (0, 0, 0, 0) := by
  constructor
  · -- Assume the equation holds, prove (x, y, z, t) = (0, 0, 0, 0)
    intro h
    have h1 : (x - y / 2 - z / 2 - t / 2) ^ 2 + (y - x / 2) ^ 2 + (z - x / 2) ^ 2 + (t - x / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t),
          sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (x - 2 * t), sq_nonneg (x - (y + z + t) / 2),
          h, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t)]
    -- Each square must be zero since they are non-negative
    have h2 : x - y / 2 - z / 2 - t / 2 = 0 := by 
      nlinarith [h1, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t)]
    have h3 : y - x / 2 = 0 := by 
      nlinarith [h1, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t)]
    have h4 : z - x / 2 = 0 := by 
      nlinarith [h1, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t)]
    have h5 : t - x / 2 = 0 := by 
      nlinarith [h1, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t)]
    -- Solve for x, y, z, t
    have hx : x = 0 := by
      nlinarith
    have hy : y = 0 := by
      nlinarith
    have hz : z = 0 := by
      nlinarith
    have ht : t = 0 := by
      nlinarith
    -- Prove the tuple is (0, 0, 0, 0)
    simp [Prod.ext_iff, hx, hy, hz, ht]
  · -- Assume the tuple is (0, 0, 0, 0), prove the equation
    rintro ⟨rfl, rfl, rfl, rfl⟩
    all_goals norm_num