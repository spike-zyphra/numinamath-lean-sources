import Mathlib

/- Let $k$ be an integer greater than 1. Let $N$ be a natural number, and let $a,b,c$ be integers. Suppose $a,b,c$ are all divisible by $k$, and suppose $N = a^2+b^2+c^2$.
Prove that there exist integers $x,y,z$ such that $N=x^2+y^2+z^2$ and at least one of $x,y,z$ is divisible by $k$. -/
theorem number_theory_635050 (k : ℤ) (hk : 1 < k) (N : ℤ) (hN : 0 ≤ N) (a b c : ℤ) (h₁ : k ∣ a) (h₂ : k ∣ b) (h₃ : k ∣ c) (h₄ : N = a ^ 2 + b ^ 2 + c ^ 2) :
    ∃ x y z : ℤ, N = x ^ 2 + y ^ 2 + z ^ 2 ∧ (k ∣ x ∨ k ∣ y ∨ k ∣ z) := by
  use a, b, c
  simp [h₄, h₁]