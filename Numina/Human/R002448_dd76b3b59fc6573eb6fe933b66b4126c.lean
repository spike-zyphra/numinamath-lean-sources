import Mathlib
/-- Four coins are picked out of a piggy bank that contains a collection of pennies, nickels, dimes, and quarters. Which of the following could not be the total value of the four coins, in cents?

$\textbf{(A)}\ 15 \qquad \textbf{(B)}\ 25 \qquad \textbf{(C)}\ 35 \qquad \textbf{(D)}\ 45 \qquad \textbf{(E)}\ 55$ -/
theorem number_theory_93555 (n m p q : ℕ) (h₀ : n + m + p + q = 4) :
n * 1 + m * 5 + p * 10 + q * 25 ≠ 15 := by
  -- Hence the smallest coin we can use is a nickel, and thus the smallest amount we can get is $4\cdot 5 = 20$. Therefore the option that is not reachable is $\boxed{15}$ $\Rightarrow$ $(A)$.
  omega