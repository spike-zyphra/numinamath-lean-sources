import Mathlib

/- If $Q = 5+2i$, $E = i$, and $D = 5-2i$, find $Q\cdot E \cdot D$. -/
theorem algebra_10536 {Q E D : ℂ} (hQ : Q = 5 + 2 * .I) (hE : E = .I) (hD : D = 5 - 2 * .I) :
    Q * E * D = 29 * .I := by
  rw [hQ, hE, hD]; simp [Complex.ext_iff]; norm_num