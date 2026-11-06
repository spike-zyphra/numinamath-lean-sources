import Mathlib

/- Suppose $x, y, z, t$ are real numbers such that $\begin{cases} 
|x + y + z -t |\le 1 \\
|y + z + t - x|\le 1 \\
|z + t + x - y|\le 1 \\
|t + x + y - z|\le 1 \end{cases}$
Prove that $x^2 + y^2 + z^2 + t^2 \le 1$. -/
theorem inequalities_69410 (x y z t : ℝ)
    (h₁ : abs (x + y + z - t) ≤ 1)
    (h₂ : abs (y + z + t - x) ≤ 1)
    (h₃ : abs (z + t + x - y) ≤ 1)
    (h₄ : abs (t + x + y - z) ≤ 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 ≤ 1 := by 
  cases' le_total 0 (x + y + z - t) with h h <;>
  cases' le_total 0 (y + z + t - x) with h' h' <;>
  cases' le_total 0 (z + t + x - y) with h'' h'' <;>
  cases' le_total 0 (t + x + y - z) with h''' h''' <;>
  simp_all only [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
  nlinarith