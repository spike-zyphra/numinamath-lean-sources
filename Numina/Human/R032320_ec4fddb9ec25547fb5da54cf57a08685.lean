import Mathlib

/- If
\begin{align*}
a + b + c &= 1, \\
a^2 + b^2 + c^2 &= 2, \\
a^3 + b^3 + c^3 &= 3,
\end{align*}find $a^4 + b^4 + c^4.$ -/
theorem algebra_16029 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a^2 + b^2 + c^2 = 2)
    (h₂ : a^3 + b^3 + c^3 = 3) :
    a^4 + b^4 + c^4 = 25 / 6 := by
  have h₃ : a = 1 - b - c := by linarith
  simp [h₃] at h₁ h₂ ⊢
  nlinarith
