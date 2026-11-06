import Mathlib

theorem algebra_297505 {k : ℤ} (hk : k ≠ 0) :
    ∃ x : ℚ, k * x ^ 2 + (2 * k + 3) * x + 1 = 0 ↔ k = -2 := by 
  use -1
  constructor
  · -- Assume $k * (-1)^2 + (2 * k + 3) * (-1) + 1 = 0$, prove $k = -2$
    intro h
    have h1 : (k : ℚ) = -2 := by
      linarith
    have h2 : k = -2 := by
      exact_mod_cast h1
    assumption
  · -- Assume $k = -2$, prove $k * (-1)^2 + (2 * k + 3) * (-1) + 1 = 0$
    intro h
    rw [h]
    norm_num