import Mathlib

theorem algebra_213118 (x y z t : ℝ) : x^2 + y^2 + z^2 + t^2 = x * (y + z + t) ↔ (x, y, z, t) = (0, 0, 0, 0) := by
  constructor
  · -- Assume equality, prove equation
    intro h
    have h1 : (y - x / 2) ^ 2 + (z - x / 2) ^ 2 + (t - x / 2) ^ 2 + (x ^ 2 / 4) = 0 := by
      nlinarith
    have h2 : (y - x / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y - x / 2), sq_nonneg (z - x / 2), sq_nonneg (t - x / 2), sq_nonneg (x ^ 2 / 4)]
    have h3 : (z - x / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y - x / 2), sq_nonneg (z - x / 2), sq_nonneg (t - x / 2), sq_nonneg (x ^ 2 / 4)]
    have h4 : (t - x / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y - x / 2), sq_nonneg (z - x / 2), sq_nonneg (t - x / 2), sq_nonneg (x ^ 2 / 4)]
    have h5 : x ^ 2 / 4 = 0 := by
      nlinarith [sq_nonneg (y - x / 2), sq_nonneg (z - x / 2), sq_nonneg (t - x / 2), sq_nonneg (x ^ 2 / 4)]
    have hx : x = 0 := by
      nlinarith
    have hy : y = 0 := by
      nlinarith [hx]
    have hz : z = 0 := by
      nlinarith [hx]
    have ht : t = 0 := by
      nlinarith [hx]
    simp [hx, hy, hz, ht]
  · -- Assume equation, prove quadruple
    rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num