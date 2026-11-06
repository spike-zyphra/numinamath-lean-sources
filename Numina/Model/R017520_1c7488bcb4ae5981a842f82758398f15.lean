import Mathlib

theorem number_theory_215249 : ¬∃ x y : ℤ, 19 * x ^ 2 - 76 * y ^ 2 = 1976 := by
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have h1 : x % 2 = 0 := by
    have h_eq1 : (19 * x ^ 2 : ℤ) % 4 = (76 * y ^ 2 + 1976 : ℤ) % 4 := by
      omega
    have h6 : (19 * x ^ 2 : ℤ) % 4 = (3 * (x ^ 2) ) % 4 := by
      ring_nf
      <;> omega
    have h7 : (76 * y ^ 2 + 1976 : ℤ) % 4 = 0 := by 
      omega
    rw [h6] at h_eq1
    rw [h7] at h_eq1
    have h5 : (x ^ 2) % 4 = 0 := by
      omega
    have h8 : x % 2 = 0 := by
      by_contra h
      push_neg at h
      have h_n1 : x % 2 = 1 := by
        omega
      have h_n2 : x ^ 2 % 4 = 1 := by
        have h1 : x % 4 = 1 ∨ x % 4 = 3 := by 
          omega
        rcases h1 with (h1 | h1)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.add_emod, Int.mul_emod]
      omega
    assumption
  have hx2 : ∃ k : ℤ, x = 2 * k := by
    refine' ⟨x / 2, by omega⟩
  rcases hx2 with ⟨k, hk⟩
  have h_eq2 : 19 * (2 * k) ^ 2 - 76 * y ^ 2 = 1976 := by
    rw [show x = 2 * k by linarith [hk]] at h_eq
    all_goals linarith
  have h_eq3 : k ^ 2 - y ^ 2 = 26 := by
    nlinarith
  have h_eq4 : (k - y) * (k + y) = 26 := by
    nlinarith
  have h_eq5 : k - y ∣ 26 := by 
    use k + y
    all_goals linarith
  have h_eq6 : k - y ≤ 26 := by 
    apply Int.le_of_dvd (show 0 < (26 : ℤ) by norm_num) h_eq5
  have h_eq7 : k - y ≥ -26 := by 
    have h_eq8 : -(k - y) ∣ 26 := by
      exact Int.neg_dvd.2 h_eq5
    have h_eq9 : -(k - y) ≤ 26 := by
      apply Int.le_of_dvd (show 0 < (26 : ℤ) by norm_num) h_eq8
    omega
  interval_cases h5 : k - y <;> omega