import Mathlib
/- Given the three numbers $x, y=x^x, z=x^{(x^x)}$ with $.9< x <1.0$. Arranged in order of increasing magnitude, they are:

$\textbf{(A)}\ x, z, y \qquad\textbf{(B)}\ x, y, z \qquad\textbf{(C)}\ y, x, z \qquad\textbf{(D)}\ y, z, x \qquad\textbf{(E)}\ z, x, y$  -/
theorem inequalities_75933 (x y z : ℝ) (hx : 0.9 < x ∧ x < 1.0) (hy : y = x ^ x) (hz : z = x ^ (x ^ x)) : x < z ∧ z < y:= by
    -- Extract the bounds on x into separate hypotheses
    rcases hx with ⟨hx1, hx2⟩
    -- Simplify the numerical bounds
    norm_num at hx1 hx2
    -- Derive that x is positive from the lower bound
    replace hx1 : 0 < x:= by linarith
    -- Substitute the definitions of y and z
    subst y z
    -- Prove that x < x^x using the fact that x < 1 implies x^x > x
    have h1:= Real.rpow_lt_rpow_of_exponent_gt hx1 hx2 (show x < 1 by exact hx2)
    simp at h1
    -- Prove that x^x < 1 using the fact that x < 1
    have h2 : x ^ x < 1 ^ x:= by refine Real.rpow_lt_rpow (by linarith) hx2 hx1
    simp at h2
    -- Prove that x < x^(x^x) using the fact that x^x < 1
    have h3:= Real.rpow_lt_rpow_of_exponent_gt hx1 hx2 (show x ^ x < 1 by exact h2)
    simp at h3
    -- Prove that x^(x^x) < x^x using the fact that x < x^x
    have h4:= Real.rpow_lt_rpow_of_exponent_gt hx1 hx2 (show x < x ^ x by exact h1)
    -- Combine the inequalities to get x < z < y
    exact ⟨h3, h4⟩
