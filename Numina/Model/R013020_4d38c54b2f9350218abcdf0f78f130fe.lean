import Mathlib

theorem inequalities_277494 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x < 2) (hyz : y < 2) (hzz : z < 2) (hsum : x^2 + y^2 + z^2 = 3) :
    3 / 2 < (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) ∧
    (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) < 3 ∧
    2 ≤ (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) := by

  constructor
  · -- First, we prove the lower bound: $\frac{3}{2} < \cdots$
    have h1 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) > 3 / 2 := by
      have h2 : 0 < x + 2 := by nlinarith
      have h3 : 0 < y + 2 := by nlinarith
      have h4 : 0 < z + 2 := by nlinarith
      have h5 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 / 2 > 0 := by
        have h6 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 / 2 =
            (2 * ((1 + y^2) * (y + 2) * (z + 2) + (1 + z^2) * (x + 2) * (z + 2) + (1 + x^2) * (x + 2) * (y + 2)) - 3 * (x + 2) * (y + 2) * (z + 2)) / (2 * (x + 2) * (y + 2) * (z + 2)) := by
          field_simp
          ring
        rw [h6]
        apply div_pos
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hsum, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
        positivity
      linarith
    linarith
  constructor
  · -- Second, we prove the upper bound: $\cdots < 3$
    have h1 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) < 3 := by
      have h2 : 0 < x + 2 := by nlinarith
      have h3 : 0 < y + 2 := by nlinarith
      have h4 : 0 < z + 2 := by nlinarith
      have h5 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 < 0 := by
        have h6 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 3 =
            ((1 + y^2) * (y + 2) * (z + 2) + (1 + z^2) * (x + 2) * (z + 2) + (1 + x^2) * (x + 2) * (y + 2) - 3 * (x + 2) * (y + 2) * (z + 2)) / ((x + 2) * (y + 2) * (z + 2)) := by
          field_simp
          ring
        rw [h6]
        apply div_neg_of_neg_of_pos
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          hsum, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
        positivity
      linarith
    linarith
  · -- Third, we prove the strengthened lower bound: $2 \leq \cdots$
    have h2 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) ≥ 2 := by
      have h2 : 0 < x + 2 := by nlinarith
      have h3 : 0 < y + 2 := by nlinarith
      have h4 : 0 < z + 2 := by nlinarith
      have h5 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 2 ≥ 0 := by
        have h6 : (1 + y^2) / (x + 2) + (1 + z^2) / (y + 2) + (1 + x^2) / (z + 2) - 2 =
            ((1 + y^2) * (y + 2) * (z + 2) + (1 + z^2) * (x + 2) * (z + 2) + (1 + x^2) * (x + 2) * (y + 2) - 2 * (x + 2) * (y + 2) * (z + 2)) / ((x + 2) * (y + 2) * (z + 2)) := by
          field_simp
          ring
        rw [h6]
        apply div_nonneg
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hsum, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
        positivity
      linarith
    linarith