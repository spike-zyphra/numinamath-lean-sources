import Mathlib

theorem inequalities_160457 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (p q r : ℝ) (hp : p = x + y + z) (hq : q = x * y + y * z + z * x)
    (hr : r = x * y * z) :
    (p ^ 2 ≥ 3 * q) ∧ (p ^ 3 ≥ 27 * r) ∧ (p * q ≥ 9 * r) ∧
    (q ^ 2 ≥ 3 * p * r) ∧ (p ^ 2 * q + 3 * p * r ≥ 4 * q ^ 2) ∧
    (p ^ 3 + 9 * r ≥ 4 * p * q) ∧ (p * q ^ 2 ≥ 2 * p ^ 2 * r + 3 * q * r) ∧
    (p * q ^ 2 + 3 * q * r ≥ 4 * p ^ 2 * r) ∧
    (2 * q ^ 3 + 9 * r ^ 2 ≥ 7 * p * q * r) ∧
    (p ^ 4 + 4 * q ^ 2 + 6 * p * r ≥ 5 * p ^ 2 * q) := by

  constructor
  · -- Prove p^2 ≥ 3*q
    rw [hp, hq]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p^3 ≥ 27*r
    rw [hp, hr]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - x), sq_nonneg (x + y + z - y), sq_nonneg (x + y + z - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p*q ≥ 9*r
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove q^2 ≥ 3*p*r
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p^2*q + 3*p*r ≥ 4*q^2
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p^3 + 9*r ≥ 4*p*q
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p*q^2 ≥ 2*p^2*r + 3*q*r
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove p*q^2 + 3*q*r ≥ 4*p^2*r
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · -- Prove 2*q^3 + 9*r^2 ≥ 7*p*q*r
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  · -- Prove p^4 + 4*q^2 + 6*p*r ≥ 5*p^2*q
    rw [hp, hq, hr]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x * (x - y) + y * (y - z) + z * (z - x)), sq_nonneg ((x - y) * (x - y + z)), sq_nonneg ((y - z) * (y + z - x)), sq_nonneg ((z - x) * (z + x - y)),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]