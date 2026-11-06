import Mathlib

theorem algebra_2198 {p q : ℝ} (hp : p > 0) (hq : q < 0) :
    (∃! x : ℝ, x > 0 ∧ x ^ 2 + p * x + q = 0) := by

  have h1 : p ^ 2 - 4 * q > 0 := by
    nlinarith

  have h2 : ∃ x : ℝ, x > 0 ∧ x ^ 2 + p * x + q = 0 := by
    have h3 : p ^ 2 - 4 * q > 0 := h1
    use (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2
    constructor
    · -- Show root is positive
      have h4 : Real.sqrt (p^2 - 4 * q) > p := by
        nlinarith [Real.sqrt_nonneg (p^2 - 4 * q), Real.sq_sqrt (show 0 ≤ p^2 - 4 * q by linarith)]
      nlinarith
    · -- Show root satisfies the equation
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith)]

  have h3 : ∀ x : ℝ, x > 0 ∧ x ^ 2 + p * x + q = 0 → x = (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2 := by
    intro x h
    rcases h with ⟨hx_pos, heq⟩
    have h4 : p ^ 2 - 4 * q > 0 := h1
    have h5 : x ^ 2 + p * x + q = 0 := heq
    have h5' : (x - (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2) * (x - (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2) = 0 := by
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith), heq]
    cases' (mul_eq_zero.mp h5') with h6 h7
    · -- h6: x = (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2
      linarith
    · -- h7: x = (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2
      have h8 : x = (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2 := by linarith
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith), hx_pos]

  use (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2
  constructor
  · -- Show that (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2 is a positive root
    have h4 : Real.sqrt (p^2 - 4 * q) > p := by
      nlinarith [Real.sqrt_nonneg (p^2 - 4 * q), Real.sq_sqrt (show 0 ≤ p^2 - 4 * q by linarith)]
    constructor
    · -- Show root is positive
      nlinarith
    · -- Show root satisfies the equation
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith)]
  · -- Show that it's unique
    intro x h
    rcases h with ⟨hx_pos, heq⟩
    have h4 : p ^ 2 - 4 * q > 0 := h1
    have h5 : x ^ 2 + p * x + q = 0 := heq
    have h5' : (x - (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2) * (x - (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2) = 0 := by
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith), heq]
    cases' (mul_eq_zero.mp h5') with h6 h7
    · -- h6: x = (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2
      linarith
    · -- h7: x = (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2
      have h8 : x = (-p - Real.sqrt (p ^ 2 - 4 * q)) / 2 := by linarith
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ p ^ 2 - 4 * q by linarith), hx_pos]