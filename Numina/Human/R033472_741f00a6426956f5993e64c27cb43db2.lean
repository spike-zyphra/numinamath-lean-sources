import Mathlib

/-- Brianna is using part of the money she earned on her weekend job to buy several equally-priced
CDs. She used one fifth of her money to buy one third of the CDs. What fraction of her money will
she have left after she buys all the CDs?
$\textbf{(A) }\ \frac15 \qquad\textbf{(B) }\ \frac13 \qquad\textbf{(C) }\ \frac25 \qquad\textbf{(D)
}\ \frac23 \qquad\textbf{(E) }\ \frac45$ -/
theorem algebra_1162 (m : ℚ) (c : ℕ) (p : ℚ) (h : m / 5 = p * c / 3) : (m - p*c) = m * 2/5 := by
  -- Let $m$ be Brianna's money, $c$ is total number of CDs and $p$ is the price of one CD.
  -- We have the equation $\frac 15 m = \frac 13 p c$.
  -- Therefore, $\frac 35 m = p c$
  replace h : m * 3 / 5 = p * c := by linarith

  -- Thus, the money left over is $m - p c = m - \frac 35 m = \frac 25 m$
  replace h : m - p*c = m * 2/5 := by
    calc _ = m - m * 3/5 := by rw [←h]
         _ = m * 2/5 := by linarith

  -- So, the answer is $\frac 25$
  exact h