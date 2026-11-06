import Mathlib

theorem number_theory_223696 (x y z : ℤ) :
    (x - y)^3 + (y - z)^3 + (z - x)^3 ≠ 30 := by
  intro h
  have eq1 : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 =
      3 * ((x - y) * (y - z) * (z - x)) := by
    ring_nf
  rw [eq1] at h
  have eq2 : (x - y) * (y - z) * (z - x) = 10 := by
    linarith
  have h1 : (x - y) * (y - z) * (z - x) = 10 := eq2
  have h2 : x - y ∣ 10 := by
    use (y - z) * (z - x)
    linarith
  have h3 : y - z ∣ 10 := by
    use (x - y) * (z - x)
    linarith
  have h4 : z - x ∣ 10 := by
    use (x - y) * (y - z)
    linarith
  have h5 : x - y ≤ 10 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h6 : x - y ≥ -10 := by
    have h7 : -(x - y) ∣ 10 := by
      exact Int.neg_dvd.2 h2
    have h8 : -(x - y) ≤ 10 := by
      apply Int.le_of_dvd (by norm_num) h7
    omega
  have h7 : y - z ≤ 10 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h8 : y - z ≥ -10 := by
    have h9 : -(y - z) ∣ 10 := by
      exact Int.neg_dvd.2 h3
    have h10 : -(y - z) ≤ 10 := by
      apply Int.le_of_dvd (by norm_num) h9
    omega
  have h9 : z - x ≤ 10 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h10 : z - x ≥ -10 := by
    have h11 : -(z - x) ∣ 10 := by
      exact Int.neg_dvd.2 h4
    have h12 : -(z - x) ≤ 10 := by
      apply Int.le_of_dvd (by norm_num) h11
    omega
  interval_cases h : x - y <;> interval_cases k : y - z <;> omega