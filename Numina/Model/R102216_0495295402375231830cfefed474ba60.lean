import Mathlib

theorem algebra_161336 {a b c x : ℝ} (ha : a + x ^ 2 = 2015) (hb : b + x ^ 2 = 2016)
    (hc : c + x ^ 2 = 2017) (habc : a * b * c = 24) :
    a / (b * c) + b / (a * c) + c / (a * b) - 1 / a - 1 / b - 1 / c = 1 / 8 := by
  have h1 : b - a = 1 := by
    nlinarith
  have h2 : c - b = 1 := by
    nlinarith
  have hb_eq : b = a + 1 := by linarith
  have hc_eq : c = a + 2 := by
    linarith [hb_eq, h2]
  -- Substitute into the equation a * b * c = 24
  have eq1 : a * b * c = 24 := habc
  rw [hb_eq, hc_eq] at eq1
  -- Now solve the equation to get a = 2
  have ha_eq : a = 2 := by
    have eq2 : a ^ 3 + 3 * a ^ 2 + 2 * a - 24 = 0 := by
      ring_nf at eq1 ⊢
      linarith
    have h1 : a ^ 3 + 3 * a ^ 2 + 2 * a - 24 = (a - 2) * (a ^ 2 + 5 * a + 12) := by
      ring
    rw [h1] at eq2
    cases (mul_eq_zero.1 eq2) with
    | inl h2 =>
      linarith
    | inr h2 =>
      -- The quadratic factor has no real roots
      have h4 : (a + 5 / 2) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      -- Show that a^2 + 5 * a + 12 = 0 has no real roots
      nlinarith
  have hab : b = 3 := by
    nlinarith [hb_eq, ha_eq]
  have hac : c = 4 := by
    nlinarith [hc_eq, ha_eq]
  have h6 : a ≠ 0 := by linarith [ha_eq]
  have h7 : b ≠ 0 := by linarith [hab]
  have h8 : c ≠ 0 := by linarith [hac]
  -- Substitute these values into the original expression
  rw [show a = 2 by linarith [ha_eq], show b = 3 by linarith [hab], show c = 4 by linarith [hac]]
  norm_num
  all_goals linarith