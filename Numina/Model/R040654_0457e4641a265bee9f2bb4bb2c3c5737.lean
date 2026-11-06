import Mathlib

theorem algebra_189729 (x y : ℤ) :
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33 := by
  have h1 : x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 =
          (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y) := by
    ring
  rw [h1] at *
  by_contra h
  have h2 : (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y) = 33 := h
  have h3 : (x + 3 * y) ∣ 33 := by
    use (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h4 : (x + 3 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h5 : (x + 3 * y) ≥ -33 := by
    have h6 : -(x + 3 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h3
    have h7 : -(x + 3 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h6
    linarith
  have h6 : (x - y) ∣ 33 := by
    use (x + 3 * y) * (x + y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h7 : (x - y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h6
  have h8 : (x - y) ≥ -33 := by
    have h9 : -(x - y) ∣ 33 := by
      exact Int.neg_dvd.2 h6
    have h10 : -(x - y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h9
    linarith
  have h9 : (x + y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h10 : (x + y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h9
  have h11 : (x + y) ≥ -33 := by
    have h12 : -(x + y) ∣ 33 := by
      exact Int.neg_dvd.2 h9
    have h13 : -(x + y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h12
    linarith
  have h14 : (x - 2 * y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x + y) * (x + 2 * y)
    linarith
  have h15 : (x - 2 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h14
  have h16 : (x - 2 * y) ≥ -33 := by
    have h17 : -(x - 2 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h14
    have h18 : -(x - 2 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h17
    linarith
  have h19 : (x + 2 * y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y)
    linarith
  have h20 : (x + 2 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h19
  have h21 : (x + 2 * y) ≥ -33 := by
    have h22 : -(x + 2 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h19
    have h23 : -(x + 2 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h22
    linarith
  have h8 : x ≤ 34 := by
    omega
  have h9 : x ≥ -34 := by
    omega
  have h10 : y ≤ 34 := by
    omega
  have h11 : y ≥ -34 := by
    omega
  interval_cases x <;> interval_cases y
  <;> omega