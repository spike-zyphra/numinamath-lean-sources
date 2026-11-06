import Mathlib

open scoped List

theorem algebra_138682 : ∀ x y : ℤ,
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33 := by
  intro x y h
  have h1 : x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 =
    (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y) := by
    ring
  rw [h1] at h
  have h2 : (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y) = 33 := h
  have h3 : (x + 3 * y) ∣ 33 := by
    use (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h4 : (x - y) ∣ 33 := by
    use (x + 3 * y) * (x + y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h5 : (x + y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h6 : (x - 2 * y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x + y) * (x + 2 * y)
    linarith
  have h7 : (x + 2 * y) ∣ 33 := by
    use (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y)
    linarith
  have h8 : (x + 3 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h9 : (x + 3 * y) ≥ -33 := by
    have h12 : -(x + 3 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h3
    have h13 : -(x + 3 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h12
    linarith
  have h10 : (x - y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h11 : (x - y) ≥ -33 := by
    have h12 : -(x - y) ∣ 33 := by
      exact Int.neg_dvd.2 h4
    have h13 : -(x - y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h12
    linarith
  have h12 : (x + y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h5
  have h13 : (x + y) ≥ -33 := by
    have h14 : -(x + y) ∣ 33 := by
      exact Int.neg_dvd.2 h5
    have h15 : -(x + y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h14
    linarith
  have h14 : (x - 2 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h6
  have h15 : (x - 2 * y) ≥ -33 := by
    have h16 : -(x - 2 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h6
    have h17 : -(x - 2 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h16
    linarith
  have h16 : (x + 2 * y) ≤ 33 := by
    apply Int.le_of_dvd (by norm_num) h7
  have h17 : (x + 2 * y) ≥ -33 := by
    have h18 : -(x + 2 * y) ∣ 33 := by
      exact Int.neg_dvd.2 h7
    have h19 : -(x + 2 * y) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h18
    linarith
  have h18 : x ≤ 34 := by
    omega
  have h19 : x ≥ -34 := by
    omega
  have h20 : y ≤ 34 := by
    omega
  have h21 : y ≥ -34 := by
    omega
  interval_cases x <;> interval_cases y 
    <;> omega