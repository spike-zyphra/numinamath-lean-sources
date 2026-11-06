import Mathlib

theorem algebra_9347 (x : ℝ) : x ^ 2 < x ↔ x ∈ Set.Ioo 0 1 := by
  simp only [Set.mem_Ioo]
  constructor
  · -- Assume x^2 < x, prove 0 < x < 1
    intro h
    -- We can rewrite the inequality as x^2 - x < 0
    have h1 : x ^ 2 - x < 0 := by linarith
    -- This factors as x(x - 1) < 0
    have h2 : x * (x - 1) < 0 := by nlinarith
    -- Now we need to deduce where the product is negative
    cases mul_neg_iff.mp h2 with
    | inl h3 =>
      constructor
      · linarith
      · linarith
    | inr h4 =>
      linarith
  · -- Assume 0 < x < 1, prove x^2 < x
    rintro ⟨h1, h2⟩
    -- Since 0 < x < 1, we can rewrite the inequality as x^2 - x < 0
    have h3 : x * (x - 1) < 0 := by 
      nlinarith
    nlinarith