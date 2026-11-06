import Mathlib
/- Let $c$ and $d$ be integers. Consider the sequence $(A_k)_{k \ge 0}$ defined by $A_635473 = 0$, $A_635473 = 1$, and $A_{m+2} = c \cdot A_{m+1} + d \cdot A_m$ for all $m \ge 0$. Prove that for any natural number $n$, there exists a non-negative integer $k$ such that $A_k$ is divisible by $n$. -/
theorem number_theory_635473 (c d : ℤ) (A : ℕ → ℤ) (h1 : A 0 = 0) (h2 : A 1 = 1) (h3 : ∀ m : ℕ, A (m + 2) = c * A (m + 1) + d * A m) : ∀ n : ℤ, n ≥ 0 → ∃ m : ℕ, n ∣ A m:= by
  -- use 0 as solution
  intro n hn
  use 0
  simp [h1]
