import Mathlib


theorem number_theory_114813 :
    {(x, y) : ℤ × ℤ | x^2 - y^2 = 1997} =
    {(999, 998), (999, -998), (-999, -998), (-999, 998)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies x² - y² = 1997
    rintro H
    have h1 : x^2 - y^2 = 1997 := H
    have h2 : (x - y) * (x + y) = 1997 := by
      linarith
    have h3 : (x - y) ∣ 1997 := by
      use (x + y)
      linarith
    have h4 : (x - y) = 1 ∨ (x - y) = -1 ∨ (x - y) = 1997 ∨ (x - y) = -1997 := by
      have h5 : (x - y) ∣ 1997 := h3
      have h6 : (x - y) ≤ 1997 := by
        exact Int.le_of_dvd (by norm_num) h5
      have h7 : (x - y) ≥ -1997 := by
        have h8 : -(x - y) ∣ 1997 := by
          exact Int.neg_dvd.2 h5
        have h9 : -(x - y) ≤ 1997 := by
          exact Int.le_of_dvd (by norm_num) h8
        linarith
      interval_cases (x - y) <;> norm_num at h5 ⊢
      <;> omega
    rcases h4 with (h4 | h4 | h4 | h4)
    · -- x - y = 1, hence x + y = 1997
      have h5 : (x + y) = 1997 := by
        rw [h4] at h2
        linarith
      have hx : x = 999 := by
        omega
      have hy : y = 998 := by
        omega
      simp [hx, hy]
    · -- x - y = -1, hence x + y = -1997
      have h5 : (x + y) = -1997 := by
        rw [h4] at h2
        linarith
      have hx : x = -999 := by
        omega
      have hy : y = -998 := by
        omega
      simp [hx, hy]
    · -- x - y = 1997, hence x + y = 1
      have h5 : (x + y) = 1 := by
        rw [h4] at h2
        linarith
      have hx : x = 999 := by
        omega
      have hy : y = -998 := by
        omega
      simp [hx, hy]
    · -- x - y = -1997, hence x + y = -1
      have h5 : (x + y) = -1 := by
        rw [h4] at h2
        linarith
      have hx : x = -999 := by
        omega
      have hy : y = 998 := by
        omega
      simp [hx, hy]
  · -- Show that these four pairs satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check that (999, 998) satisfies the equation
      norm_num
    · -- Check that (999, -998) satisfies the equation
      norm_num
    · -- Check that (-999, -998) satisfies the equation
      norm_num
    · -- Check that (-999, 998) satisfies the equation
      norm_num