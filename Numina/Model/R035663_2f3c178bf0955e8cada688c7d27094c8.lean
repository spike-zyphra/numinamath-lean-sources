import Mathlib
theorem algebra_241101: {(x,y): ℤ × ℤ | x > 0 ∧ y > 0 ∧ 2 * x^2 + 5 * y^2 = 11 * (x * y - 11)}
 = {(14,27)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is a solution, prove (x, y) = (14, 27)
    rintro ⟨hx, hy, heq⟩
    have eq1 : (2 * x - y) * (x - 5 * y) = -121 := by
      nlinarith
    have h2 : (2 * x - y) ∣ -121 := by
      use (x - 5 * y)
      all_goals linarith [eq1]
    have h3 : (2 * x - y) ∣ 121 := by
      exact Int.dvd_neg.mp h2
    have h4 : (2 * x - y) ≤ 121 := by 
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (2 * x - y) ≥ -121 := by
      have h6 : (-(2 * x - y)) ∣ 121 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(2 * x - y) ≤ 121 := by 
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    interval_cases h : (2 * x - y) <;> omega
  · -- Show that (14, 27) is a solution
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num