import Mathlib

theorem algebra_205149 (a b c d : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : a^2 - 10 * c * a - 11 * d = 0)
    (h2 : b^2 - 10 * c * b - 11 * d = 0) (h3 : c^2 - 10 * a * c - 11 * b = 0)
    (h4 : d^2 - 10 * a * d - 11 * b = 0) : a + b + c + d = 1210 := by
  have eq1 : a + b = 10 * c := by
    have h5 : a^2 - b^2 = 10 * c * (a - b) := by
      nlinarith
    have h6 : a + b = 10 * c := by
      apply (mul_left_inj' (show a - b ≠ 0 by
        intro h
        apply ha
        linarith)).mp
      linarith
    exact h6
  have eq2 : c + d = 10 * a := by
    have h6 : c^2 - d^2 = 10 * a * (c - d) := by
      nlinarith
    have h7 : c + d = 10 * a := by
      apply (mul_left_inj' (show c - d ≠ 0 by
        intro h
        apply hf
        linarith)).mp
      linarith
    exact h7
  have eq3 : b = 10 * c - a := by
    linarith [eq1]
  have eq4 : d = 10 * a - c := by
    linarith [eq2]
  rw [eq4] at h1
  rw [eq3] at h3
  have eq5 : a^2 - 10 * a * c - 11 * (10 * a - c) = 0 := by
    linarith [h1]
  have eq6 : c^2 - 10 * a * c - 11 * (10 * c - a) = 0 := by
    linarith [h3]
  have eq7 : (a - c) * (a + c - 121) = 0 := by
    nlinarith [eq5, eq6]
  cases' (mul_eq_zero.mp eq7) with h8 h9
  · -- case $a - c = 0$, which means $a = c$, a contradiction
    exfalso
    apply hb
    linarith [h8]
  · -- case $a + c - 121 = 0$, which means $a + c = 121$
    have eq8 : a + c = 121 := by
      linarith [h9]
    have eq9 : a + b + c + d = 10 * (a + c) := by
      linarith [eq1, eq2]
    rw [eq9]
    rw [eq8]
    all_goals norm_num