import Mathlib

theorem inequalities_46254 (x y : ℝ) (h₀ : x ^ 2 ≥ y) (h₁ : y ^ 2 ≥ x) :
    x / (y ^ 2 + 1) + y / (x ^ 2 + 1) ≤ 1 := by
  have h2 : x / (y ^ 2 + 1) + y / (x ^ 2 + 1) - 1 ≤ 0 := by
    have h3 : 0 < y ^ 2 + 1 := by
      nlinarith [sq_nonneg y]

    have h4 : 0 < x ^ 2 + 1 := by
      nlinarith [sq_nonneg x]

    have h4' : x / (y ^ 2 + 1) + y / (x ^ 2 + 1) - 1 =
        (x * (x ^ 2 + 1) + y * (y ^ 2 + 1) - (x ^ 2 + 1) * (y ^ 2 + 1)) / ((y ^ 2 + 1) * (x ^ 2 + 1)) := by
      field_simp
      <;> ring

    rw [h4']

    apply div_nonpos_of_nonpos_of_nonneg
    · -- Numerator: Show that $x(x^2+1)+y(y^2+1)-(x^2+1)(y^2+1) \le0$
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x ^ 2 - y), sq_nonneg (y ^ 2 - x), mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁)]
    · -- Denominator is $\ge0$
      positivity
  linarith [h2]