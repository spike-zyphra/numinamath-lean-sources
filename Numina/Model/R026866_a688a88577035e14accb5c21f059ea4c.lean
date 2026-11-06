import Mathlib

open Real

theorem algebra_231754 {a b x : ℝ} : exp ((a + b) * x) = exp (a * x) * exp (b * x) ∧
    ∀ k : ℕ, exp (k * x) = (exp x)^k := by
  constructor
  · -- Prove that exp((a+b)*x) = exp(a*x)*exp(b*x).
    have h1 : (a + b) * x = a * x + b * x := by
      ring
    rw [h1]
    rw [Real.exp_add]
  · -- Prove that ∀ k : ℕ, exp(k*x) = (exp(x))^k.
    intro k
    rw [exp_nat_mul]
    all_goals simp