import Mathlib

/- Let $\mathrm{a}, \mathrm{b}>0$ such that $\mathrm{a}+\mathrm{b}=1$. Show that $\left(\mathrm{a}+\frac{1}{a}\right)^{2}+\left(b+\frac{1}{b}\right)^{2} \geqslant \frac{25}{2}$.-/
theorem inequalities_149345 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  -- Show that a² + b² ≥ 1 / 2.
  have h₀ : a ^ 2 + b ^ 2 ≥ 1 / 2 := by
    -- Basically we use the fact that a + b = 1 and (a - b)² ≥ 0.
    nlinarith [sq_nonneg (a - b)]
  -- Show that 4ab ≤ 1 by similar way.
  have h₁ : 4 * (a * b) ≤ 1 := by
    nlinarith [sq_nonneg (a - b)]
  -- We have 4 ≤ 1 / ab.
  replace h₁ := (le_div_iff₀ (by positivity)).mpr h₁
  -- Show that 1 / a² + 1 / b² ≥ 8.
  replace h₁ : 1 / (a ^ 2) + 1 / (b ^ 2) ≥ 8 := by
    calc
      _ = (1 / a - 1 / b) ^ 2 + 2 * (1 / (a * b)) := by
        field_simp
        ring
      _ ≥ 8 := by
        linarith [sq_nonneg (1 / a - 1 / b)]
  -- Change the expression (a + 1 / a)² + (b + 1 / b)² to a² + b² + (1 / a² + 1 / b²) + 4, and then use previous results.
  calc
    _ = a ^ 2 + b ^ 2 + (1 / (a ^ 2) + 1 / (b ^ 2)) + 4 := by
      field_simp
      ring
    _ ≥ 25 / 2 := by
      linear_combination (h₀ + h₁)