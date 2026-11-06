import Mathlib

theorem algebra_120965 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * (x + y + z) = 4 * p ∧ 2 * (x * y + y * z + z * x) = 2 * q ↔
    p ^ 2 ≥ 3 * q := by
  by_cases h : p ^ 2 ≥ 3 * q
  · -- Assume p^2 >= 3q
    use (p - Real.sqrt (p ^ 2 - 3 * q)) / 3,
      (p - Real.sqrt (p ^ 2 - 3 * q)) / 3,
      p - 2 * ((p - Real.sqrt (p ^ 2 - 3 * q)) / 3)
    constructor
    · -- Assume edge lengths satisfy required conditions, prove p^2 >= 3q
      intro h
      rcases h with ⟨hx, hy, hz, h1, h2⟩
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 3 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 3 * q by nlinarith)]
    · -- Assume p^2 >= 3q, prove edge lengths satisfy required conditions
      intro hpq
      constructor
      · -- Show 0 < x
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 3 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 3 * q by nlinarith)]
      constructor
      · -- Show 0 < y
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 3 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 3 * q by nlinarith)]
      constructor
      · -- Show 0 < z
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 3 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 3 * q by nlinarith)]
      constructor
      · -- Show 4 * (x + y + z) = 4 * p
        ring_nf
      · -- Show 2 * (x * y + y * z + z * x) = 2 * q
        nlinarith [Real.sqrt_nonneg (p ^ 2 - 3 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 3 * q by nlinarith)]
  · -- Assume p^2 < 3q
    use 0, 0, 0
    simp at *
    <;> nlinarith