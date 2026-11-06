import Mathlib

theorem algebra_319351 (f : ℝ → ℝ) (hf : f = fun x => 2 * x - x ^ 2 - 2 / x) :
    {x | 0 < x ∧ f x = 0}.encard = 0 := by
  have h1 : {x | 0 < x ∧ f x = 0} = ∅ := by
    ext x
    simp [hf]
    intro hx hx2
    have h3 : x ^ 3 - 2 * x ^ 2 + 2 > 0 := by
      have h1 : x ^ 3 - 2 * x ^ 2 + 2 > 0 := by
        have h1 : x ^ 3 - 2 * x ^ 2 + 2 > 0 := by
          have h1 : x ^ 3 - 2 * x ^ 2 + 2 > 0 := by
            have h1 : x ^ 3 - 2 * x ^ 2 + 2 > 0 := by
              have h2 : x ^ 2 * (x - 2) + 2 > 0 := by
                have h2 : x ^ 2 * (x - 2) + 2 > 0 := by
                  nlinarith [sq_nonneg (x - 4 / 3), sq_nonneg (x - 2), sq_nonneg (x - 1)]
                linarith
              nlinarith
            linarith
          linarith
        linarith
      linarith
    have h2 : x ^ 3 - 2 * x ^ 2 + 2 = 0 := by
      field_simp at hx2
      nlinarith
    linarith
  rw [h1]
  simp