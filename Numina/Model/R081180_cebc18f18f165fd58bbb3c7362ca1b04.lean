import Mathlib

theorem algebra_99173 (x y : ℤ) :
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33 := by 
  have h1 : x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 =
    (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y) * (x + 2 * y) := by
    ring_nf
  rw [h1] at *
  -- Assume equality
  by_contra h
  -- Assign a variable to the equation
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
  have h8 : (x - y) ∣ 33 := by 
    use (x + 3 * y) * (x + y) * (x - 2 * y) * (x + 2 * y)
    linarith
  have h9 : (x - y) ≤ 33 := by 
    apply Int.le_of_dvd (by norm_num) h8
  have h10 : (x - y) ≥ -33 := by 
    have h11 : -(x - y) ∣ 33 := by 
      exact Int.neg_dvd.2 h8
    have h12 : -(x - y) ≤ 33 := by 
      apply Int.le_of_dvd (by norm_num) h11
    linarith
  have h11 : (x + y) ∣ 33 := by 
    use (x - 2 * y) * (x + 2 * y) * (x - y) * (x + 3 * y)
    linarith
  have h12 : (x + y) ≤ 33 := by 
    apply Int.le_of_dvd (by norm_num) h11
  have h13 : (x + y) ≥ -33 := by 
    have h14 : -(x + y) ∣ 33 := by 
      exact Int.neg_dvd.2 h11
    have h15 : -(x + y) ≤ 33 := by 
      apply Int.le_of_dvd (by norm_num) h14
    linarith
  have h16 : (x - 2 * y) ∣ 33 := by 
    use (x + 3 * y) * (x - y) * (x + y) * (x + 2 * y)
    linarith
  have h17 : (x - 2 * y) ≤ 33 := by 
    apply Int.le_of_dvd (by norm_num) h16
  have h18 : (x - 2 * y) ≥ -33 := by 
    have h19 : -(x - 2 * y) ∣ 33 := by 
      exact Int.neg_dvd.2 h16
    have h20 : -(x - 2 * y) ≤ 33 := by 
      apply Int.le_of_dvd (by norm_num) h19
    linarith
  have h21 : (x + 2 * y) ∣ 33 := by 
    use (x + 3 * y) * (x - y) * (x + y) * (x - 2 * y)
    linarith
  have h22 : (x + 2 * y) ≤ 33 := by 
    apply Int.le_of_dvd (by norm_num) h21
  have h23 : (x + 2 * y) ≥ -33 := by 
    have h24 : -(x + 2 * y) ∣ 33 := by 
      exact Int.neg_dvd.2 h21
    have h25 : -(x + 2 * y) ≤ 33 := by 
      apply Int.le_of_dvd (by norm_num) h24
    linarith
  have h40 : x ≤ 34 := by 
    omega
  have h41 : x ≥ -34 := by 
    omega
  have h42 : y ≤ 34 := by 
    omega
  have h43 : y ≥ -34 := by 
    omega
  interval_cases x <;> interval_cases y 
  <;> omega