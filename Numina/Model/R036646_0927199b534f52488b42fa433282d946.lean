import Mathlib

theorem number_theory_135636 : ¬∃ x y : ℤ, 23*x^2-92*y^2=3128 := by
  rintro ⟨x, y, h⟩
  have h1 : 23 * x^2 - 92 * y^2 = 3128 := h
  have h2 : x^2 - 4 * y^2 = 136 := by
    nlinarith
  have h3 : x % 2 = 0 := by
    by_contra h
    have h4 : x % 2 = 1 := by omega
    have h5 : x^2 % 2 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    omega
  have h6 : ∃ k : ℤ, x = 2 * k := by
    refine' ⟨x / 2, by omega⟩
  rcases h6 with ⟨k, hk⟩
  have h7 : k^2 - y^2 = 34 := by
    rw [hk] at h2
    nlinarith
  have h8 : (k - y) * (k + y) = 34 := by
    nlinarith
  have h9 : k - y ∣ 34 := by
    use k + y
    all_goals nlinarith
  have h10 : k - y ∣ 34 := h9
  have h11 : k - y ≤ 34 := by 
    apply Int.le_of_dvd (by norm_num) h10
  have h12 : k - y ≥ -34 := by
    have h13 : -(k - y) ∣ 34 := by 
      exact Int.neg_dvd.2 h10
    have h14 : -(k - y) ≤ 34 := by 
      apply Int.le_of_dvd (by norm_num) h13
    linarith
  interval_cases h15 : k - y <;> omega