import Mathlib

theorem algebra_609728 (a b k: ℝ) (hk: k > 0) (hab: b = 3 * a)
    (hk_area: k = a * b) (hk_per: k = 2 * (a + b)): k = (64: ℝ) / 3 := by
  -- From hk_area and hab, we have k = 3 * a^2.
  have eq1 : k = 3 * a^2 := by
    rw [hk_area]
    rw [hab]
    nlinarith
  -- From the perimeter equation: k = 2 * (a + b) = 8*a
  have eq2 : k = 8 * a := by
    nlinarith [hk_per, hab]
  -- Now equate k from eq1 and eq2.
  -- We have k = 3*a^2 and k = 8*a, so 3*a^2 = 8*a.
  have eq3 : 3 * a^2 = 8 * a := by
    nlinarith [eq1, eq2]
  -- Rearranging: 3*a^2 - 8*a = 0
  -- Factor: a*(3*a - 8) = 0
  have eq4 : a * (3 * a - 8) = 0 := by
    nlinarith [eq3]
  -- Therefore either a = 0 or 3*a - 8 = 0
  cases' (mul_eq_zero.1 eq4) with ha1 ha2
  · -- Case a = 0 leads to contradiction with k > 0
    have ha : a = 0 := by
      linarith
    -- From k = 8 * a, which is k = 0, which contradicts k > 0
    have hk0 : k = 0 := by
      nlinarith [eq2, ha]
    -- contradiction with hk: k > 0
    linarith
  · -- 3*a - 8 = 0 => a = 8/3
    -- Now compute k from k = 8 * a = 8 * (8/3) = 64/3
    have ha2' : a = 8 / 3 := by
      linarith
    -- Therefore k = 64/3
    have hk1 : k = 64 / 3 := by
      nlinarith [eq2, ha2']
    -- Now prove the goal k = (64 : ℝ) / 3
    linarith