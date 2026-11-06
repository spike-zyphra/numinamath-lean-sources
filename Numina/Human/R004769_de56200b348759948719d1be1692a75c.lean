import Mathlib

/- \begin{array}{c}
f(f(n))+f(n)=2 n+3 \text {, and } f(0)=1 . \\
\text { Then } \frac{f(6) f(7) f(8) f(9) f(10)}{f(1)+f(2)+f(3)+f(4)+f(5)}=
\end{array} -/
theorem algebra_320250 {f : ℕ → ℕ} (h : ∀ n, f (f n) + f n = 2 * n + 3) (hf : f 0 = 1) :
    ((f 6) * (f 7) * (f 8) * (f 9) * (f 10) / (f 1 + f 2 + f 3 + f 4 + f 5) : ℝ) = 2772 := by
  have H n : f n = n + 1 := by
    induction n with
    | zero => simp [hf]
    | succ n ih =>
      specialize h n
      simp [ih] at h
      omega
  norm_num [H]
