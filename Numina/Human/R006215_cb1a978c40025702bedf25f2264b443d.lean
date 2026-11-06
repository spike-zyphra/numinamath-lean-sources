import Mathlib

/- Let $n$ be a positive integer such that $n$ is not a perfect square. Prove that the square root of $n$ is irrational. -/
theorem number_theory_634712 (n : ℕ) (h₀ : 0 < n) (h : ¬ IsSquare n) :
    Irrational √n := by
  exact irrational_sqrt_natCast_iff.mpr h