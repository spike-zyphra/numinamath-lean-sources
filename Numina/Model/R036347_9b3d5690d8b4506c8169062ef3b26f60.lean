import Mathlib

theorem algebra_601947 (x y z a : ℝ) (ha : 0 < a)
    (h1 : x + y + z = a) (h2 : x^2 + y^2 + z^2 = a^2 / 2) :
    ¬x < 0 ∧ ¬y < 0 ∧ ¬z < 0 ∧ ¬x > 2 * a / 3 ∧ ¬y > 2 * a / 3 ∧ ¬z > 2 * a / 3 := by
  constructor
  · -- Assume x < 0, derive a contradiction
    by_contra hx
    have hx1 : x < 0 := hx
    have h3 : y + z > a := by nlinarith
    have h4 : 2 * (y ^ 2 + z ^ 2) ≥ (y + z) ^ 2 := by
      linarith [sq_nonneg (y - z)]
    have h5 : y ^ 2 + z ^ 2 ≥ (a - x) ^ 2 / 2 := by
      have h6 : y + z = a - x := by linarith
      rw [h6] at h4
      nlinarith
    have h6 : x ^ 2 + y ^ 2 + z ^ 2 ≥ x ^ 2 + (a - x) ^ 2 / 2 := by
      have h7 : y ^ 2 + z ^ 2 ≥ (a - x) ^ 2 / 2 := h5
      nlinarith
    nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x - a / 3), sq_nonneg (y - a / 3), sq_nonneg (z - a / 3)]
  constructor
  · -- Assume y < 0, derive a contradiction
    by_contra hy
    have hy1 : y < 0 := hy
    have h3 : x + z > a := by nlinarith
    have h4 : 2 * (x ^ 2 + z ^ 2) ≥ (x + z) ^ 2 := by
      linarith [sq_nonneg (x - z)]
    have h5 : x ^ 2 + z ^ 2 ≥ (a - y) ^ 2 / 2 := by
      have h6 : x + z = a - y := by linarith
      rw [h6] at h4
      nlinarith
    have h6 : x ^ 2 + y ^ 2 + z ^ 2 ≥ y ^ 2 + (a - y) ^ 2 / 2 := by
      have h7 : x ^ 2 + z ^ 2 ≥ (a - y) ^ 2 / 2 := h5
      nlinarith
    nlinarith [sq_nonneg (y), sq_nonneg (x - z), sq_nonneg (x + z - a), sq_nonneg (y - x), sq_nonneg (y - z), sq_nonneg (x - z), sq_nonneg (y - a / 3), sq_nonneg (x - a / 3), sq_nonneg (z - a / 3)]
  constructor
  · -- Assume z < 0, derive a contradiction
    by_contra hz
    have hz1 : z < 0 := hz
    have h3 : x + y > a := by nlinarith
    have h4 : 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
      linarith [sq_nonneg (x - y)]
    have h5 : x ^ 2 + y ^ 2 ≥ (a - z) ^ 2 / 2 := by
      have h6 : x + y = a - z := by linarith
      rw [h6] at h4
      nlinarith
    have h6 : x ^ 2 + y ^ 2 + z ^ 2 ≥ z ^ 2 + (a - z) ^ 2 / 2 := by
      have h7 : x ^ 2 + y ^ 2 ≥ (a - z) ^ 2 / 2 := h5
      nlinarith
    nlinarith [sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x + y - a), sq_nonneg (z - x), sq_nonneg (z - y), sq_nonneg (x - y), sq_nonneg (z - a / 3), sq_nonneg (x - a / 3), sq_nonneg (y - a / 3)]
  constructor
  · -- Assume x > 2/3 * a, derive a contradiction
    by_contra hx
    have hx1 : x > 2 * a / 3 := by linarith
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - x), sq_nonneg (x - a / 3), sq_nonneg (y - a / 3), sq_nonneg (z - a / 3), sq_nonneg (x + y + z - a), sq_nonneg ((y - z) - (x - y)), sq_nonneg ((x - 2 * a / 3) + (y - 2 * a / 3) + (z - 2 * a / 3)), sq_nonneg ((x - 2 * a / 3) - (y - 2 * a / 3)), sq_nonneg ((x - 2 * a / 3) - (z - 2 * a / 3)), sq_nonneg ((y - 2 * a / 3) - (z - 2 * a / 3))]
  constructor
  · -- Assume y > 2/3 * a, derive a contradiction
    by_contra hy
    have hy1 : y > 2 * a / 3 := by linarith
    nlinarith [sq_nonneg (x - z), sq_nonneg (x + z - y), sq_nonneg (y - a / 3), sq_nonneg (x - a / 3), sq_nonneg (z - a / 3), sq_nonneg (x + y + z - a), sq_nonneg ((x - z) - (y - x)), sq_nonneg ((y - 2 * a / 3) + (x - 2 * a / 3) + (z - 2 * a / 3)), sq_nonneg ((y - 2 * a / 3) - (x - 2 * a / 3)), sq_nonneg ((y - 2 * a / 3) - (z - 2 * a / 3)), sq_nonneg ((x - 2 * a / 3) - (z - 2 * a / 3))]
  · -- Assume z > 2/3 * a, derive a contradiction
    by_contra hz
    have hz1 : z > 2 * a / 3 := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - z), sq_nonneg (z - a / 3), sq_nonneg (x - a / 3), sq_nonneg (y - a / 3), sq_nonneg (x + y + z - a), sq_nonneg ((x - y) - (z - x)), sq_nonneg ((z - 2 * a / 3) + (x - 2 * a / 3) + (y - 2 * a / 3)), sq_nonneg ((z - 2 * a / 3) - (x - 2 * a / 3)), sq_nonneg ((z - 2 * a / 3) - (y - 2 * a / 3)), sq_nonneg ((x - 2 * a / 3) - (y - 2 * a / 3))]