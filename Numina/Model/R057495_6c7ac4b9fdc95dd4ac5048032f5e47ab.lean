import Mathlib

theorem algebra_268398 (n : ℕ) (hn : n ≠ 0) (h : (1 / 3 : ℚ) * n + 6 = (1 / 5 : ℚ) * n) :
    n = 20 := by
  have eq1 : (n : ℚ) ≥ 0 := by exact_mod_cast show (n : ℚ) ≥ 0 by positivity
  -- Multiply both sides of the equation by 15 to eliminate denominators.
  have h1 : (n : ℚ) = -45 := by
    -- The original equation is inconsistent given the constraints.
    linarith
  have h2 : (n : ℚ) ≥ 0 := by
    exact_mod_cast show (n : ℚ) ≥ 0 by positivity
  -- The contradictory cases will prove the theorem vacuously.
  linarith