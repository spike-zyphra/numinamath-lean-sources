import Mathlib

theorem algebra_50291 {a b c : ℝ} (h : a + b + c = 0) :
    ((a ^ 2 + b ^ 2 + c ^ 2) / 2 * (a ^ 3 + b ^ 3 + c ^ 3) / 3 =
     (a ^ 5 + b ^ 5 + c ^ 5) / 5) ∧
    ((a ^ 2 + b ^ 2 + c ^ 2) / 2 * (a ^ 5 + b ^ 5 + c ^ 5) / 5 =
     (a ^ 7 + b ^ 7 + c ^ 7) / 7) := by

  -- From the fact that $a + b + c = 0$, we write $c = -a -b$ to reduce variables
  have h1 : c = -a - b := by linarith
  constructor
  · -- Prove the first identity
    rw [h1]
    ring_nf
  · -- Prove the second identity
    rw [h1]
    ring_nf