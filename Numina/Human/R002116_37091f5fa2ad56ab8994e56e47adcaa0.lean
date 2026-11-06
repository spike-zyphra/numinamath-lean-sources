import Mathlib

/- Maureen is keeping track of the mean of her quiz scores this semester. If Maureen scores an $11$ on the next quiz, her mean will increase by $1$. If she scores an $11$ on each of the next three quizzes, her mean will increase by $2$. What is the mean of her quiz scores currently? $\textbf{(A) }4\qquad\textbf{(B) }5\qquad\textbf{(C) }6\qquad\textbf{(D) }7\qquad\textbf{(E) }8$ -/
theorem algebra_65411 (x : ℝ) (n : ℕ) (h1 : (x * n + 11) / (n + 1) = x + 1) (h2 : (x * n + 11 + 11 + 11) / (n + 3) = x + 2) :
x = 7 := by
  -- multiply h1
  have lw : (x * ↑n + 11) / (↑n + 1) * (↑n + 1) = (x + 1) * (↑n + 1) := by rw [h1]
  rw [div_mul_cancel₀ _ (by norm_cast), mul_add, add_mul, mul_one] at lw
  -- multiply h2
  have wl : (x * ↑n + 11 + 11 + 11) / (↑n + 3) * (↑n + 3) = (x + 2) * (↑n + 3) := by rw [h2]
  rw [div_mul_cancel₀ _ (by norm_cast), mul_add, add_mul] at wl
  -- solve automatically
  linarith