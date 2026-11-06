import Mathlib

/- Given that point $P$ lies on the line $x+2y-1=0$, point $Q$ lies on the line $x+2y+3=0$, the midpoint of $PQ$ is $M\left( {{x}_{0}}, {{y}_{0}} \right)$, and ${{y}_{0}}>{{x}_{0}}+2$, then the range of $\frac{{{y}_{0}}}{{{x}_{0}}}$ is ___          ___. -/
theorem algebra_12136 (P Q M : ℝ × ℝ)
    (hP : P.1 + 2 * P.2 - 1 = 0) (hQ : Q.1 + 2 * Q.2 + 3 = 0)
    (hM : M.1 = (P.1 + Q.1) / 2 ∧ M.2 = (P.2 + Q.2) / 2)
    (hM' : M.2 > M.1 + 2) :
    -1 / 2 < (M.2 / M.1) ∧ (M.2 / M.1) < -1 / 5 := by

  have h1 : P.1 = 1 - 2 * P.2 := by linarith
  have h2 : Q.1 = -3 - 2 * Q.2 := by linarith
  have h3 : M.1 = (P.1 + Q.1) / 2 := hM.1
  rw [h1, h2] at h3
  have eq3 : M.2 = (P.2 + Q.2) / 2 := by linarith [hM.2]
  have eq4 : P.2 + Q.2 = 2 * M.2 := by
    linarith [eq3]
  have h4 : M.1 = -1 - (P.2 + Q.2) := by
    linarith
  rw [eq4] at h4
  have eq1 : M.1 = -1 - 2 * M.2 := by linarith
  have eq2 : M.1 + 2 * M.2 = -1 := by linarith
  have h2 : M.1 < 0 := by
    nlinarith [hM']
  constructor
  · -- Proof that -1/2 < (y0/x0)
    have h1 : -1 / 2 < (M.2 / M.1) := by
      have eq3 : M.1 + 2 * M.2 = -1 := eq2
      have h3 : M.1 < 0 := h2
      have eq4 : M.2 = (-1 - M.1)/2 := by
        linarith
      rw [eq4]
      apply (lt_div_iff_of_neg' (by linarith)).mpr
      nlinarith [hM']
    exact h1
  · -- Proof that (y0/x0) < -1/5
    have h5 : (M.2 / M.1) < -1 / 5 := by
      have eq3 : M.1 + 2 * M.2 = -1 := eq2
      have h3 : M.1 < 0 := h2
      have eq4 : M.2 = (-1 - M.1)/2 := by
        linarith
      rw [eq4]
      apply (div_lt_iff_of_neg' (by linarith)).mpr
      nlinarith [hM']
    exact h5