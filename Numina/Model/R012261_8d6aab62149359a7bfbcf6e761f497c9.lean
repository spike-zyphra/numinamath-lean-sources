import Mathlib

lemma lemma1 {x y: ℤ}: 3 * y ^ 2 + 3 * x * y + x + y = (x + y) * (3 * y + 1) := by
  ring

theorem algebra_196962: {(x, y): ℤ × ℤ | 3 * y ^ 2 + 3 * x * y + x + y = 2019} =
  {(-221, 224), (2019, 0)} := by
  ext ⟨x, y⟩
  simp [lemma1]
  constructor
  · -- Assume (x, y) satisfies the equation
    rintro h
    have h1 : (x + y) * (3 * y + 1) = 2019 := by
      linarith
    have h2 : (3 * y + 1) ∣ 2019 := by
      use x + y
      all_goals linarith
    have h3 : (3 * y + 1) ≤ 2019 := by
      exact Int.le_of_dvd (by norm_num) h2
    have h4 : (3 * y + 1) ≥ -2019 := by
      have h6 : -(3 * y + 1) ∣ 2019 := by
        exact Int.neg_dvd.2 h2
      have h7 : -(3 * y + 1) ≤ 2019 := by
        exact Int.le_of_dvd (by norm_num) h6
      linarith
    have h8 : y ≤ 673 := by
      omega
    have h9 : y ≥ -673 := by
      omega
    interval_cases y <;> omega
  · -- Show that these points satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      norm_num