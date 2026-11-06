import Mathlib

/- Let $a, b, c > 0$ and $abc = 1$. Prove that
\[(1+a^3)^4(1+b^3)^4(1+c^3)^4 \ge 512(1+a^4)(1+b^4)(1+c^4).\] -/
theorem my_favorite_theorem (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 ≥
    512 * (1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4) := by
  -- It suffices to show that (1 + x ^ 3) ^ 4 ≥ 8 * x ^ 4 * (1 + x ^ 4) for all x > 0.
  suffices H (x : ℝ) (hx : 0 < x) : (1 + x ^ 3) ^ 4 ≥ 8 * x ^ 4 * (1 + x ^ 4)
  {
    -- We use it for a, b, c.
    have h₁ := H a ha
    have h₂ := H b hb
    have h₃ := H c hc
    -- Multiply the inequalities.
    let f := ![8 * a ^ 4 * (1 + a ^ 4), 8 * b ^ 4 * (1 + b ^ 4), 8 * c ^ 4 * (1 + c ^ 4)]
    let g := ![(1 + a ^ 3) ^ 4, (1 + b ^ 3) ^ 4, (1 + c ^ 3) ^ 4]
    have h0 (i : Fin 3) (_ : i ∈ Finset.univ) : 0 ≤ f i := by
      fin_cases i
      all_goals
        simp [f]
        positivity
    have h1 (i : Fin 3) (_ : i ∈ Finset.univ) : f i ≤ g i := by
      fin_cases i
      all_goals
        simp [f, g]
        assumption
    have H := Finset.prod_le_prod h0 h1
    simp [Finset.prod, Finset.sum, f, g] at H
    -- We have a ^ 4 * b ^ 4 * c ^ 4 = 1.
    rw [ge_iff_le, show (512 : ℝ) = 8 * 8 * 8 * (a ^ 4 * b ^ 4 * c ^ 4) by norm_num [← mul_pow, habc]]
    -- It is almost exact what we want.
    convert H using 1 <;> ac_rfl
  }
  -- To prove the univariate inequality, we calculate LHS - RHS = (x - 1) ^ 2 * (a polynomial with all positive coefficients).
  -- So it is nonnegative.
  have H : 0 ≤ (x - 1) ^ 2 * (x ^ 10 + 2 * x ^ 9 + 3 * x ^ 8 + 8 * x ^ 7 + 5 * x ^ 6 + 2 * x ^ 5 + 5 * x ^ 4 + 8 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1) := by positivity
  linarith
