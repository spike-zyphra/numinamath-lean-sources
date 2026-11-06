import Mathlib

/- If $x$ and $y$ are positive real numbers for which $(x + y)^2 + (x - y)^2 = 10$ and $(x + y)^4 + (x - y)^4 = 98$, what is the value of $xy$? Express your answer in simplest radical form. -/
theorem algebra_21962 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : (x + y)^2 + (x - y)^2 = 10) (h2 : (x + y)^4 + (x - y)^4 = 98) :
    x * y = Real.sqrt 6 := by 
  have h3 : x^2 + y^2 = 5 := by linarith
  have h4 : x^2 * y^2 = 6 := by nlinarith
  have h5 : x * y = Real.sqrt 6 := by
    rw [sq, sq] at h4
    apply Eq.symm
    rw [Real.sqrt_eq_iff_mul_self_eq]
    all_goals nlinarith
  exact h5