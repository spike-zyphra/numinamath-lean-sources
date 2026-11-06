import Mathlib

/-
Problem

Given the system of equations in terms of $x$ and $y$: $\left\{\begin{array}{l}x+2y-6=0\\ x-2y+mx+5=0\end{array}\right.$, if the solutions of the system have $x$ as an integer and $m$ as an integer, then the value of $m$ is ______.
-/

/-
Solution

To solve the given system of equations for $x$ and $y$ with the condition that $x$ is an integer and $m$ is an integer, we proceed as follows:

Given system of equations:
\[
\begin{align*}
x + 2y - 6 &= 0 \quad &(1)\\
x - 2y + mx + 5 &= 0 \quad &(2)
\end{align*}
\]

Adding equation (1) and equation (2) to eliminate $y$, we get:
\[
x + 2y - 6 + x - 2y + mx + 5 = 0
\]
Simplifying the above equation, we get:
\[
2x + mx = 1
\]
This can be further simplified to:
\[
(2 + m)x = 1
\]
Solving for $x$, we have:
\[
x = \frac{1}{2 + m}
\]

Given that $x$ is an integer and $m$ is also an integer, for $x$ to be an integer, the denominator $(2 + m)$ must divide $1$ without leaving any remainder. The only divisors of $1$ are $\pm 1$. Therefore, we set $2 + m$ equal to these divisors:
\[
2 + m = \pm 1
\]

Solving for $m$ when $2 + m = 1$:
\[
m = 1 - 2 = -1
\]

Solving for $m$ when $2 + m = -1$:
\[
m = -1 - 2 = -3
\]

Therefore, the possible values for $m$ are $-1$ and $-3$. Hence, the final answer is encapsulated as:
\[
\boxed{-1 \text{ or } -3}
\]
-/

theorem algebra_9056 {x y m : ℤ} (h1 : x + 2 * y - 6 = 0) (h2 : x - 2 * y + m * x + 5 = 0) :
  m = -1 ∨ m = -3 := by

  -- prove that 1 = x * (m + 2)
  have h2: (x + 2 * y - 6) + (x - 2 * y + m * x + 5) = 0 := by rewrite [h1, h2]; simp
  have h3: (2+m)*x = (x + 2 * y - 6) + (x - 2 * y + m * x + 5) + 1 := by ring
  rw [h2] at h3
  simp at h3
  rw [mul_comm, add_comm] at h3
  symm at h3

  --  x >= 0
  by_cases ca: x >= 0
  have x_mod1: x∣1 := ⟨m+2, h3⟩
  have xis1 : x = 1 := Int.eq_one_of_dvd_one ca x_mod1
  rw [xis1] at h3
  simp at h3
  have h3: m = 1 - 2 := by rw [h3]; simp
  simp at h3
  exact Or.inl h3

  -- -x >= 0
  have ca : 0 ≤ -x := le_of_lt (Left.neg_pos_iff.mpr (lt_of_not_ge ca))
  rw [<- neg_mul_neg] at h3
  have neg_x_mod1: -x∣1 := ⟨-(m+2), h3⟩
  have xis1 : -x = 1 := Int.eq_one_of_dvd_one ca neg_x_mod1
  rw [xis1] at h3
  have h3: m=-1-2 := by rw [h3]; simp
  simp at h3
  exact Or.inr h3
