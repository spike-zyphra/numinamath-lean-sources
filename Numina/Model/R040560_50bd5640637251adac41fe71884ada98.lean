import Mathlib

theorem algebra_249154 (x : ℝ) (h : Real.sin x ^ 10 + Real.cos x ^ 10 = 11 / 36) :
    Real.sin x ^ 14 + Real.cos x ^ 14 = 41 / 216 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have eq2 : (Real.sin x ^ 2) ^5 + (Real.cos x ^2) ^5 = 11 / 36 := by
    nlinarith [h]
  have eq3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
    nlinarith
  have eq4 : (Real.sin x ^ 2) * (Real.cos x ^ 2) = 1 / 6 := by
    have eq5 : (Real.sin x ^ 2) ^5 + (Real.cos x ^ 2) ^5 =
        (Real.sin x ^ 2 + Real.cos x ^ 2)^5 - 5 * ((Real.sin x ^ 2) * (Real.cos x ^ 2)) * (Real.sin x ^ 2 + Real.cos x ^ 2)^3 + 5 * ((Real.sin x ^ 2) * (Real.cos x ^ 2)) ^ 2 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by
      ring
    rw [show Real.sin x ^ 2 + Real.cos x ^ 2 = 1 by linarith [h1]] at eq5
    rw [eq5] at eq2
    have eq7 : ((Real.sin x ^ 2) * (Real.cos x ^ 2) - 5 / 6) * ((Real.sin x ^ 2) * (Real.cos x ^ 2) - 1 / 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq7) with eq8 eq9
    · -- If $u \cdot v = \frac{5}{6}$.
      have h4 : (Real.sin x ^ 2) * (Real.cos x ^ 2) ≤ (1 / 4 : ℝ) := by
        nlinarith [sq_nonneg (Real.sin x ^ 2 - Real.cos x ^ 2)]
      nlinarith [eq8]
    · -- $u \cdot v = \frac{1}{6}$.
      linarith
  have eq8 : Real.sin x ^ 14 + Real.cos x ^ 14 = (Real.sin x ^ 2) ^7 + (Real.cos x ^ 2) ^7 := by
    ring_nf
  rw [eq8]
  have eq9 : (Real.sin x ^ 2) ^7 + (Real.cos x ^ 2) ^7 =
      (Real.sin x ^ 2 + Real.cos x ^ 2)^7
      - 7 * ((Real.sin x ^ 2) * (Real.cos x ^ 2)) * (Real.sin x ^ 2 + Real.cos x ^ 2)^5
      + 14 * ((Real.sin x ^ 2) * (Real.cos x ^ 2)) ^ 2 * (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 3
      - 7 * ((Real.sin x ^ 2) * (Real.cos x ^ 2)) ^ 3 * (Real.sin x ^ 2 + Real.cos x ^ 2) := by 
    ring
  rw [eq9]
  rw [show Real.sin x ^ 2 + Real.cos x ^ 2 = 1 by nlinarith [h1]]
  rw [eq4]
  <;> norm_num