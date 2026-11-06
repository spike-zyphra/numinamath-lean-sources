import Mathlib

/- What is the sum of the prime factors of 85,085? -/
theorem algebra_21516 {n : ℕ} (hn : n = 85085) :
    ∑ p in n.primeFactors, p = 53 := by subst n; native_decide
