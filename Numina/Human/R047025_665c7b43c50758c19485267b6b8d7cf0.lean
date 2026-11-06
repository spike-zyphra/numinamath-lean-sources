import Mathlib
open Real
/- 11. Let $x \in \mathbf{R}$, for the function $f(x)$ satisfying the condition $f\left(x^{2}+1\right)=x^{4}+5 x^{2}-3$. Then, for all $x \in \mathbf{R}, f\left(x^{2}-1\right)=$ $\qquad$ -/
theorem algebra_324654 {f : ℝ → ℝ} (h : ∀ y, f (1+y^2) =- 3+ y^2*5 + y^4 ) (x : ℝ) (hx : - 1+x^2 ≥ 1) :
    f (-1+x^2) = - 9+x^2+x^4 := by
  have h0 :∀ y≥ 1, f (y) = y^2 + 3 * y - 7 := by
    intro y hy
    have hy' : y - 1 ≥ 0 := by
      linarith
    let a := sqrt (y-1)
    have ha : y=a^2 + 1 := by
      unfold a
      rw[sq_sqrt]
      · linarith
      · exact hy'
    rw[ha]
    ring_nf
    exact h a
  have h1 : f (-1 + x ^ 2) = (-1 + x ^ 2) ^ 2 + 3 * (-1 + x ^ 2) - 7 :=h0 (-1 + x ^ 2) (by
    linarith)
  ring_nf at h1
  linarith