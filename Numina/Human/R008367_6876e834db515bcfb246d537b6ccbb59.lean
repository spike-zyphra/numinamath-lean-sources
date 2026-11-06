import Mathlib

/- Given $\left\{\begin{array}{l}x=3\\ y=2\end{array}\right.$ is a solution to the system of linear equations $\left\{\begin{array}{l}mx+ny=36\\ nx+my=9\end{array}\right.$, then the cube root of $m-n$ is ______. -/
theorem algebra_8996 {m n : ℝ} (h : m * 3 + n * 2 = 36 ∧ n * 3 + m * 2 = 9) :
    (m - n) ^ ((1 : ℝ) / 3) = 3 := by
  -- Solve the system of equations using linarith
  have ⟨hm, hn⟩ : m = 18 ∧ n = -9 := by constructor <;> linarith
  -- Substitute m = 18 and n = -9 into the goal and simplify
  subst m n
  rw [(by norm_num : 18 - -9 = (3 : ℝ) ^ (3 : ℝ)), ← Real.rpow_mul (by norm_num)]
  norm_num
