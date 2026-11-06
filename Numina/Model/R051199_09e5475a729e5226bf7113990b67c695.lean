import Mathlib

theorem algebra_99284 : IsGreatest {x : ℝ | abs (x^2 - 4 * x - 39601) ≥ abs (x^2 + 4 * x - 39601)} 199 := by
  constructor
  · -- Show that 199 is in the set
    show abs (199^2 - 4 * (199 : ℝ) - 39601) ≥ abs (199^2 + 4 * (199 : ℝ) - 39601)
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that the largest element in the set is 199
    intro x hx
    have h : abs (x^2 - 4 * x - 39601) ≥ abs (x^2 + 4 * x - 39601) := hx
    have h1 : (x^2 - 4 * x - 39601)^2 ≥ (x^2 + 4 * x - 39601)^2 := by 
      apply sq_le_sq.mpr
      exact h
    -- After squaring both sides and subtracting we get x * (-16x^2 + 633616) ≥ 0.
    have h2 : (x^2 - 4 * x - 39601)^2 - (x^2 + 4 * x - 39601)^2 ≥ 0 := by linarith
    -- From the difference we can derive to the polynomial.
    have h3 : x * (-16 * x ^ 2 + 633616 ) ≥ 0 := by
      nlinarith [sq_nonneg (x^2 - 4 * x - 39601), sq_nonneg (x^2 + 4 * x - 39601), sq_nonneg (x ^ 2 - 39601), sq_nonneg x]
    -- From the polynomial we derive that x ≤ 199.
    nlinarith [sq_nonneg (x ^ 2 - 39601), sq_nonneg (x - 199), sq_nonneg (x + 199), sq_nonneg (x * (x - 199)), sq_nonneg (x * (x + 199)), sq_nonneg ((x) ^ 2 * (x - 199)), sq_nonneg ((x) ^ 2 * (x + 199)), sq_nonneg (x)]