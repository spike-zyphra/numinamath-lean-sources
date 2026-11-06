import Mathlib
theorem algebra_605287 {a b c d : ℝ} (h1 : a * b * c - d = 1) (h2 : b * c * d - a = 2)
(h3 : c * d * a - b = 3) (h4 : d * a * b - c = -6) : a + b + c + d ≠ 0:= by
  intro h
  have h5 : d = -a - b - c := by linarith
  rw [h5] at h1 h2 h3 h4
  have eq1 : a * b * c + a + b + c = 1 := by linarith
  have eq2 : (a + b) * (b + c) * (c + a) = 0 := by
    nlinarith [sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  cases' (mul_eq_zero.mp eq2) with eq3 eq4
  · cases' (mul_eq_zero.mp eq3) with eq5 eq6
    · -- Case where $a + b = 0$
      have ha : a = -b := by linarith
      rw [ha] at eq1 h2 h3 h4
      have eq3a : c * (1 - b ^ 2) = 1 := by
        nlinarith
      have eq4a : b * (1 - c ^ 2) = 2 := by
        nlinarith
      have eq5a : b * (c ^ 2 - 1) = 3 := by
        nlinarith
      nlinarith
    · -- Case where $b + c = 0$
      have hb : b = -c := by linarith
      rw [hb] at eq1 h2 h3 h4
      have ha : a = 1 := by
        nlinarith
      have hc2 : c ^ 2 = 3 := by
        nlinarith
      nlinarith
  · -- Case where $c + a = 0$
    have hc : c = -a := by linarith
    rw [hc] at eq1 h2 h3 h4
    have eq3a : b * (1 - a ^ 2) = 1 := by
      nlinarith
    have eq5a : b * (a ^ 2 - 1) = 3 := by
      nlinarith
    nlinarith