import Mathlib

/- The graphs of the equations

$$
\begin{aligned}
y & =-x+8 \\
173 y & =-289 x+2021
\end{aligned}
$$

on the Cartesian plane intersect at $(a, b)$. Find $a+b$.-/
theorem algebra_610346 (a b : ℝ) (h : {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} = {(a, b)}) : a + b = 8 := by
  -- It suffices to show that {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} = {(637 / 116, 291 / 116)}.
  suffices {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} = {(637 / 116, 291 / 116)} by
    rw [h] at this
    simp at this
    linarith
  -- Now we show that {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} = {(637 / 116, 291 / 116)}.
  ext ⟨a, b⟩
  simp
  -- Break the goal into two parts and use linarith to solve simultaneous equations.
  apply Iff.intro
  all_goals
    intro h
    exact ⟨by linarith, by linarith⟩
