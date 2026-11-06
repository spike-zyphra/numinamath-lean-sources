import Mathlib
/- Let $U$ be a positive integer such that $20$ divides $U$.
Let $M$ be the number of multiples of $5$ in the range $[1, U]$ inclusive.
Let $N$ be the number of multiples of $20$ in the range $[1, U]$ inclusive.
Show that the value of $10 \cdot M \div N$ is $40$. -/
theorem number_theory_636610 (u M N : ℕ) (hu : u > 0) (h : 20 ∣ u) (hM : M = u / 5) (hN : N = u / 20) : 10 * M / N = 40:= by
  -- Extract the factor k where u = 20k using the divisibility hypothesis
  rcases h with ⟨k, hk⟩
  -- Substitute u with 20k
  subst u
  -- Simplify the expression for N
  norm_num at hN
  -- Rewrite M in terms of k using arithmetic
  rw [show 20 * k / 5 = 4 * k by omega] at hM
  -- Substitute the values of M and N
  subst M N
  -- Use the positivity hypothesis
  simp at hu
  -- Prove that 10 * (4 * k) = 40 * k to complete the proof
  suffices 10 * (4 * k) = 40 * k by rw [this] ; exact Nat.mul_div_left 40 hu
  -- Solve the arithmetic equation
  omega
