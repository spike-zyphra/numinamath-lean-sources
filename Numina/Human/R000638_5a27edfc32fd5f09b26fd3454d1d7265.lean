import Mathlib

/- If $x$ is a positive integer such that $1^{x+2} + 2^{x+1} + 3^{x-1} + 4^x = 1170$, what is the value of $x$? -/
theorem algebra_13511 (x : ℕ) (hx : x > 0) (h : 1^(x + 2) + 2^(x + 1) + 3^(x - 1) + 4^x = 1170) :
    x = 5 := by
  have h₁ : x = 5 := by
    match x with
    | 0 => contradiction
    | 1 => contradiction
    | 2 => contradiction
    | 3 => contradiction
    | 4 => contradiction
    | 5 => rfl
    | x + 6 =>
      simp [Nat.pow_succ, Nat.pow_zero, Nat.pow_succ] at h
      ring_nf at h
      omega
  exact h₁