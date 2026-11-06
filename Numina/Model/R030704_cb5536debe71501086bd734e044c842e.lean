import Mathlib

theorem inequalities_109808 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^2 / (y * (x^2 + x * y + y^2)) ≥ (2 * x - y) / (3 * x * y)) ∧
    (x^2 / (y * (x^2 + x * y + y^2)) + y^2 / (z * (y^2 + y * z + z^2)) +
     z^2 / (x * (z^2 + x * z + x^2)) ≥ (x * y + y * z + x * z) / (3 * x * y * z)) := by
  constructor
  · -- First inequality: $\frac{x^{2}}{y\left(x^{2}+x y+y^{2}\right)} \geq \frac{2 x-y}{3 x y}$.
    have h1 : 0 < y * (x ^ 2 + x * y + y ^ 2) := by
      apply mul_pos
      linarith
      nlinarith
    have h2 : 0 < 3 * x * y := by
      positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    have h3 : 3 * x ^ 3 * y - y * (x^2 + x * y + y^2) * (2 * x - y) = y * (x - y) ^ 2 * (x + y) := by
      ring
    nlinarith [sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y)]
  · -- Second inequality: $\frac{x^{2}}{y\left(x^{2}+x y+y^{2}\right)}+\frac{y^{2}}{z\left(y^{2}+y z+z^{2}\right)}+\frac{z^{2}}{x\left(z^{2}+x z+x^{2}\right)} \geq \frac{x y+y z+x z}{3 x y z}$.
    have h1 : 0 < y * (x ^ 2 + x * y + y ^ 2) := by
      apply mul_pos
      linarith
      nlinarith
    have h4 : 0 < z * (y ^ 2 + y * z + z ^ 2) := by
      apply mul_pos
      linarith
      nlinarith
    have h7 : 0 < x * (z ^ 2 + x * z + x ^ 2) := by
      apply mul_pos
      linarith
      nlinarith
    have h8 : x^2 / (y * (x^2 + x * y + y^2)) ≥ (2 * x - y) / (3 * x * y) := by
      have h1 : 0 < y * (x ^ 2 + x * y + y ^ 2) := by
        apply mul_pos
        linarith
        nlinarith
      have h2 : 0 < 3 * x * y := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h3 : 3 * x ^ 3 * y - y * (x^2 + x * y + y^2) * (2 * x - y) = y * (x - y) ^ 2 * (x + y) := by
        ring
      nlinarith [sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y)]
    have h9 : y^2 / (z * (y^2 + y * z + z^2)) ≥ (2 * y - z) / (3 * y * z) := by
      have h10 : 0 < z * (y ^ 2 + y * z + z ^ 2) := by
        apply mul_pos
        linarith
        nlinarith
      have h11 : 0 < 3 * y * z := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h12 : 3 * y ^ 3 * z - z * (y^2 + y * z + z^2) * (2 * y - z) = z * (y - z) ^ 2 * (y + z) := by
        ring
      nlinarith [sq_nonneg (y - z), sq_nonneg (z), sq_nonneg (y + z)]
    have h10 : z^2 / (x * (z^2 + x * z + x^2)) ≥ (2 * z - x) / (3 * x * z) := by
      have h11 : 0 < x * (z ^ 2 + x * z + x ^ 2) := by
        apply mul_pos
        linarith
        nlinarith
      have h12 : 0 < 3 * x * z := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h13 : 3 * z ^ 3 * x - x * (z^2 + x * z + x^2) * (2 * z - x) = x * (z - x) ^ 2 * (z + x) := by
        ring
      nlinarith [sq_nonneg (z - x), sq_nonneg (x), sq_nonneg (z + x)]
    have h11 : (x^2 / (y * (x^2 + x * y + y^2)) + y^2 / (z * (y^2 + y * z + z^2)) + z^2 / (x * (z^2 + x * z + x^2))) ≥ ( (2 * x - y) / (3 * x * y) + (2 * y - z) / (3 * y * z) + (2 * z - x) / (3 * x * z) ) := by
      linarith [h8, h9, h10]
    have g6 : ( (2 * x - y) / (3 * x * y) + (2 * y - z) / (3 * y * z) + (2 * z - x) / (3 * x * z) ) ≥ (x * y + y * z + x * z) / (3 * x * y * z) := by
      have g8 : ( (2 * x - y) / (3 * x * y) + (2 * y - z) / (3 * y * z) + (2 * z - x) / (3 * x * z) ) = (x * y + y * z + x * z) / (3 * x * y * z) := by
        field_simp
        ring
      linarith [g8]
    linarith [h11, g6]