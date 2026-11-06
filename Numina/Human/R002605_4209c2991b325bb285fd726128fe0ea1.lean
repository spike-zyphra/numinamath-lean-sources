import Mathlib
/-- Danica drove her new car on a trip for a whole number of hours, averaging 55 miles per hour. At the beginning of the trip, $abc$ miles was displayed on the odometer, where $abc$ is a 3-digit number with $a \geq{1}$ and $a+b+c \leq{7}$. At the end of the trip, the odometer showed $cba$ miles. What is $a^2+b^2+c^2?$.

$\textbf{(A)}\ 26\qquad\textbf{(B)}\ 27\qquad\textbf{(C)}\ 36\qquad\textbf{(D)}\ 37\qquad\textbf{(E)}\ 41$ -/
theorem number_theory_96214 (a b c h : ℕ) (ha : 1 ≤ a) (hh : 0 < h) (hb : a + b + c ≤ 7)
(j : (100 * a + 10 * b + c) + 55 * h = 100 * c + 10 * b + a) :
a ^ 2 + b ^ 2 + c ^ 2 = 37 := by
  -- Because $a + b + c \le 7$, $b = 0$.
  have t : b = 0 := by omega
  subst b
  -- Because we know that $c > a$ and $a + c \le 7$ and $a \ge 1$, we find that the only possible values for $a$ and $c$ are $1$ and $6$, respectively.
  (obtain ⟨u, i⟩ | ⟨u, i⟩ : (a = 1 ∧ c = 6) ∨ (a = 6 ∧ c = 1) := by omega) <;> subst a c <;> norm_num