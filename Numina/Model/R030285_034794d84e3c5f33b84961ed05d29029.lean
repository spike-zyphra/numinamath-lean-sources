import Mathlib

theorem algebra_292058 (x : ℝ) (hx : x > 0) (h : x^3 + x^(-3 : ℤ) + x^6 + x^(-6 : ℤ) = 2754) :
    x + 1/x = 4 := by
  have h1 : x^(-3 : ℤ) = 1 / x^3 := by
    simp [zpow_neg, zpow_ofNat]
  have h2 : x^(-6 : ℤ) = 1 / x^6 := by
    simp [zpow_neg, zpow_ofNat]
  rw [h1, h2] at h
  have eq1 : x^6 + 1 / x^6 = (x^3 + 1 / x^3) ^ 2 - 2 := by
    field_simp
    <;> ring
  have eq2 : x^3 + 1 / x^3 + (x^6 + 1 / x^6) = 2754 := by
    linarith
  have h3 : x^3 + 1 / x^3 + ((x^3 + 1 / x^3) ^ 2 - 2) = 2754 := by 
    rw [eq1] at eq2
    linarith
  -- Rearrange to get quadratic
  have h4 : (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2756 = 0 := by
    nlinarith
  -- Solve quadratic
  have h5 : (x^3 + 1 / x^3 - 52) * (x^3 + 1 / x^3 + 53) = 0 := by
    nlinarith [h4]
  have h6_pos : x^3 + 1 / x^3 > 0 := by 
    have h11 : x ^ 3 > 0 := by positivity
    have h12 : (1 : ℝ) / x^3 > 0 := by positivity
    have h13 : x ^ 3 + (1 : ℝ) / x^3 > 0 := by linarith [h11, h12]
    linarith
  cases' (mul_eq_zero.mp h5) with h7 h8
  · -- Case $x^3 + 1/x^3 - 52 = 0$
    have eq3 : x^3 + 1 / x^3 = 52 := by linarith
    -- Now derive $x + 1/x = 4$.
    have eq4 : x + 1 / x = 4 := by
      have eq5 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by 
        field_simp
        <;> ring
      rw [eq3] at eq5
      have eq6 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) - 52 = 0 := by
        linarith
      have eq7 : (x + 1 / x - 4) * ((x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13) = 0 := by
        ring_nf at eq6 ⊢
        nlinarith
      cases' (mul_eq_zero.mp eq7) with eq8 eq9
      · -- Case $x + 1/x - 4 = 0$. This gives the solution.
        linarith
      · -- Case $(x + 1/x)^2 + 4(x + 1/x) + 13 = 0$.
        nlinarith [sq_nonneg ((x + 1 / x) + 2)]
    exact_mod_cast eq4
  · -- Case $x^3 + 1/x^3 + 53 = 0$
    have eq3 : x^3 + 1 / x^3 = -53 := by linarith
    nlinarith [h6_pos, eq3]