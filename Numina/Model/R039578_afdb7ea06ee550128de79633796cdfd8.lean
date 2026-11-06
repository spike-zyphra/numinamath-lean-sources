import Mathlib

theorem number_theory_23411 : gcd (gcd 3339 2961) 1491 = 21 := by
  calc
    gcd (gcd 3339 2961) 1491 = gcd 63 1491 := by
      -- Show that gcd 3339 2961 = 63
      -- We compute GCD(3339, 2961) using the Euclidean algorithm
      -- 3339 = 2961 * 1 + 378
      -- 2961 = 378 * 7 + 315
      -- 378 = 315 * 1 + 63
      -- 315 = 63 * 5 + 0
      -- Therefore, GCD(3339, 2961) = 63
      rw [gcd]
      all_goals
      native_decide
    _ = 21 := by
      -- Show that gcd 63 1491 = 21
      -- We compute GCD(63, 1491) using the Euclidean algorithm
      -- 1491 = 63 * 23 + 42
      -- 63 = 42 * 1 + 21
      -- 42 = 21 * 2 + 0
      -- Therefore, GCD(63, 1491) = 21
      rw [gcd]
      all_goals
      native_decide