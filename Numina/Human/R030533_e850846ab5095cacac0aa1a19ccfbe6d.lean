import Mathlib

/- Simplify $
\root 3 \of {x \root 3 \of {x \root 3 \of {x \sqrt{x}}}}.
$ Express your answer in simplest radical form in terms of $x$.
The following theorem proves the simplification process.
-/
theorem algebra_18928 {x : ℝ} (hx : x ≥ 0) :
    (x * (x * (x * x^ (1 / 2 : ℝ))^ (1 / 3 : ℝ))^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
  -- First, express the given expression step by step using properties of exponents.
  have : (x * (x * (x * x^ (1 / 2 : ℝ))^ (1 / 3 : ℝ))^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ)
       = (x ^ (1 : ℝ) * (x ^ (1 : ℝ) * (x ^ (1 : ℝ) * x^ (1 / 2 : ℝ))^ (1 / 3 : ℝ))^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) := by
          -- Simplify the inner powers using the exponentiation rules.
          simp

  -- Now, consider the case when x = 0.
  by_cases h: x = 0
  · -- If x = 0, we evaluate the expression directly, which simplifies to 0.
    rw [h]
    simp

  -- If x > 0, we proceed with the simplification process.
  have hx : 0 < x := by exact lt_of_le_of_ne hx fun a ↦ h (Eq.symm a)

  -- Apply the previously simplified expression.
  rw [this]

  -- Simplify the power expression (x^(3/2))^(1/3) = x^(1/2).
  have : (x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [(Real.rpow_mul hx.le _ _).symm]
    norm_num

  -- Perform the final simplification.
  simp only [this, (Real.rpow_add hx _ _).symm, show 1 + (1 / 2 : ℝ) = 3 / 2 by norm_num]
