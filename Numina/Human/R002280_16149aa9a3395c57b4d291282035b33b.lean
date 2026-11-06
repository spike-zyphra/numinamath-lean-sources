import Mathlib

/-A positive integer
n satisfies the equation (n+1)!+(n+2)!=n!⋅440.
What is the sum of the digits of n?-/

theorem algebra_81340 {n: ℕ} (h: (n + 1).factorial + (n + 2).factorial = n.factorial * 440):
    (Nat.digits n 10).sum = 10 := by

  -- we show that n = 19
  have h_eq: n = 19 := by
    rw [Nat.factorial_succ] at h
    rw [show n + 2 = n + 1 + 1 by ring] at h
    rw [Nat.factorial_succ] at h
    rw [Nat.factorial_succ] at h
    rw [show (n + 1) * n.factorial + (n + 1 + 1) * ((n + 1) * n.factorial)
        = n.factorial * ((n + 1) * (n + 3)) by ring] at h
    have o: n.factorial ≠ 0 := by
      apply Nat.factorial_ne_zero
    replace h: (n + 1) * (n + 3) = 440 := by
      apply Nat.mul_left_cancel at h
      exact h
      omega
    have ln1: 18 < n := by nlinarith
    have ln2: n < 20 := by nlinarith
    omega

-- then we compute the sum of the digits
  rw [h_eq]
  simp