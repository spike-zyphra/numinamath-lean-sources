import Mathlib

/- Solve the quadratic inequality in terms of $x$: $x^2 - (2+a)x + 2a > 0$. -/
theorem algebra_9041 {a : ℝ} (ha : a ≠ 0) :
  {x | x^2 - (2 + a) * x + 2 * a > 0} = {x | x > (max a 2) ∨ x < (min a 2)} := by

  -- Factor the quadratic expression
  have he y : y ^ 2 - (2 + a) * y + 2 * a = (y - 2) * (y - a) := by ring

  -- Prove set equality by mutual inclusion
  ext y
  constructor <;> intro h
  . -- Prove the forward direction: if x^2 - (2 + a)x + 2a > 0, then x > max(a, 2) or x < min(a, 2)
    simp_all
    -- Use the property that a product is positive iff both factors have the same sign
    rw [mul_pos_iff] at h
    aesop
  . -- Prove the backward direction: if x > max(a, 2) or x < min(a, 2), then x^2 - (2 + a)x + 2a > 0
    simp_all
    cases h with
    | inl h_1 => simp_all only [sub_pos, mul_pos_iff_of_pos_left]
    | inr h_2 => nlinarith
