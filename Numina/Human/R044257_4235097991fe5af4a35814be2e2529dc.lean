import Mathlib

theorem Algebra_609899 {p q : ℝ} (h1 : p + q = 5 / 6) (h2 : p ^ 2 + q ^ 2 + 1 / 36 = 1 / 2) (hpq : p ≥ q) :
  p = 2/3 := by 
  -- Substitute q with (5/6-p)
  have peq : p ^ 2 + (5 / 6 - p) ^ 2 + 1 / 36 = 1 / 2 := by
    rw [←h2, ←h1]
    ring
  have peq' : (p - 2 / 3) * (p - 1 / 6) = 0 := by 
    nlinarith
  -- Solve for p: p must be either 2/3 or 1/6.
  have hp : p = 2 / 3 ∨ p = 1 / 6 := by
    have aux : (p - 2 / 3) = 0 ∨ (p - 1 / 6) = 0 := by  
      apply eq_zero_or_eq_zero_of_mul_eq_zero
      exact peq'
    obtain h | h' := aux
    left; nlinarith
    right; nlinarith
  obtain h | h := hp
  exact h   -- Verify which one satisfies other conditions
  exfalso  -- Prove that p cannot be 1/6 if we need p >= q
  have qeq : q = 2 / 3:= by nlinarith
  rw [h, qeq] at hpq
  linarith
  