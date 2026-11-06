import Mathlib

theorem inequalities_29663 (x y z : ℝ) :
    x^2 + y^2 + z^2 - x * y - y * z - z * x ≥
    max (max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4)) (3 * (y - z)^2 / 4) := by
  have h9 : x^2 + y^2 + z^2 - x * y - y * z - z * x ≥ 3 * (x - y)^2 / 4 := by 
    nlinarith [sq_nonneg (x - y - (y - z)), sq_nonneg (y - z - (z - x)), sq_nonneg (z - x - (x - y)), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  -- Prove x^2 + y^2 + z^2 - x * y - y * z - z * x ≥ 3 * (y - z)^2 / 4.
  have h10 : x^2 + y^2 + z^2 - x * y - y * z - z * x ≥ 3 * (y - z)^2 / 4 := by 
    nlinarith [sq_nonneg (x - y - (y - z)), sq_nonneg (y - z - (z - x)), sq_nonneg (z - x - (x - y)), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y)]
  have h5 : max (max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4)) (3 * (y - z)^2 / 4) ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x := by
    have h6 : (3 * (x - y)^2 / 4) ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x := by linarith [h9]
    have h7 : (3 * (y - z)^2 / 4) ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x := by linarith [h10]
    have h8 : max (max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4)) (3 * (y - z)^2 / 4) ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x := by
      -- The expression is max (max A B) B which equals max A B
      have h81 : max (max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4)) (3 * (y - z)^2 / 4) = max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4) := by
        simp [max_assoc]
      rw [h81]
      -- Show max (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4) ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x
      cases max_cases (3 * (x - y)^2 / 4) (3 * (y - z)^2 / 4) with
      | inl h =>
        nlinarith [h6, h]
      | inr h =>
        nlinarith [h7, h]
    linarith
  linarith [h5]