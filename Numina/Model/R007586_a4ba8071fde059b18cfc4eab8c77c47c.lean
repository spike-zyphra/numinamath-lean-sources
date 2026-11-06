import Mathlib

theorem algebra_3344 (a b c d e f : ℤ) (h : ∀ x y : ℤ, (a * x + b * y + c) * (d * x + e * y - f) = 2 * x ^ 2 - 5 * x * y + 3 * y ^ 2 - 19 * x - 25 * y + 42) :
    a + b + c + d + e + f ≤ 12 := by
  have eq1 := h 0 0
  have eq2 := h 1 0
  have eq3 := h 0 1
  have eq4 := h 1 1
  have eq5 := h 2 0
  have eq6 := h 0 2
  have eq7 := h 2 2
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  have h1 : a * d = 2 := by
    nlinarith
  have h2 : b * e = 3 := by
    nlinarith
  have h3 : -c * f = 42 := by
    nlinarith
  have h4 : a * e + b * d = -5 := by
    nlinarith
  have h5 : -a * f + c * d = -19 := by
    nlinarith
  have h6 : -b * f + c * e = -25 := by
    nlinarith
  have h8 : a ∣ 2 := by
    use d
    nlinarith
  have h9 : b ∣ 3 := by
    use e
    nlinarith
  have h10 : c ∣ 42 := by
    use -f
    nlinarith
  have h11 : f ∣ 42 := by
    use -c
    nlinarith
  have h12 : a ≤ 2 := by
    apply Int.le_of_dvd (by norm_num) h8
  have h13 : a ≥ -2 := by
    have h21 : -a ∣ 2 := by
      exact Int.neg_dvd.2 h8
    have h22 : -a ≤ 2 := by
      apply Int.le_of_dvd (by norm_num) h21
    linarith
  have h14 : b ≤ 3 := by
    apply Int.le_of_dvd (by norm_num) h9
  have h15 : b ≥ -3 := by
    have h25 : -b ∣ 3 := by
      exact Int.neg_dvd.2 h9
    have h26 : -b ≤ 3 := by
      apply Int.le_of_dvd (by norm_num) h25
    linarith
  have h16 : c ≤ 42 := by
    apply Int.le_of_dvd (by norm_num) h10
  have h17 : c ≥ -42 := by
    have h30 : -c ∣ 42 := by
      exact Int.neg_dvd.2 h10
    have h31 : -c ≤ 42 := by
      apply Int.le_of_dvd (by norm_num) h30
    linarith
  have h18 : f ≤ 42 := by
    apply Int.le_of_dvd (by norm_num) h11
  have h19 : f ≥ -42 := by
    have h33 : -f ∣ 42 := by
      exact Int.neg_dvd.2 h11
    have h34 : -f ≤ 42 := by
      apply Int.le_of_dvd (by norm_num) h33
    linarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega