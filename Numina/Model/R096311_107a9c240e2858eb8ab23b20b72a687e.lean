import Mathlib

theorem number_theory_225183 : ¬∃ x y z : ℤ, x^2 + y^2 - z^2 + 2 * x * y = 202 := by
  rintro ⟨x, y, z, h⟩
  have h1 : (x + y) ^ 2 - z ^ 2 = 202 := by
    nlinarith
  have h2 : (x + y - z) * (x + y + z) = 202 := by
    nlinarith [h1]
  have h3 : (x + y - z) ∣ 202 := by
    use (x + y + z)
    linarith
  have h5 : (x + y - z) ≤ 202 := by
    apply Int.le_of_dvd (by norm_num) h3
  have h6 : (x + y - z) ≥ -202 := by
    have h7 : -(x + y - z) ∣ 202 := by
      exact Int.neg_dvd.2 h3
    have h8 : -(x + y - z) ≤ 202 := by
      apply Int.le_of_dvd (by norm_num) h7
    linarith
  interval_cases h9 : (x + y - z) <;> omega