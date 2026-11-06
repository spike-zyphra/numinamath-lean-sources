import Mathlib

/- Compute $\gcd(83^9+1,83^9+83^2+1)$. -/
theorem number_theory_15785 : gcd (83^9 + 1) (83^9 + 83^2 + 1) = 1 := by
  apply Eq.refl