import Mathlib

theorem number_theory_217220 : ¬∃ x y : ℤ, x^2 = 2 * y^2 - 75 * y + 5 := by
  rintro ⟨x, y, h⟩
  have eq1 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
    have h1 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
  have eq2 : y^2 % 5 = 0 ∨ y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
    have h1 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.sub_emod]
  have eq3 : x^2 % 5 = (2 * y^2) % 5 := by
    have h1 : x^2 = 2 * y^2 - 75 * y + 5 := h
    have eq3 : x^2 % 5 = (2 * y^2 - 75 * y + 5) % 5 := by 
      rw [h1]
    simp [Int.add_emod, Int.sub_emod, Int.mul_emod] at eq3 ⊢
    omega
  have eq4 : y % 5 = 0 := by
    have h : y^2 % 5 = 0 := by
      omega
    have : y % 5 = 0 := by
      have h2 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> 
        simp [pow_two, Int.mul_emod, h2, Int.add_emod, Int.sub_emod] at h <;> omega
    assumption
  have eq5 : x % 5 = 0 := by
    have h1 : x^2 % 5 = 0 := by
      omega
    have : x % 5 = 0 := by
      have h11 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega
      rcases h11 with (h11 | h11 | h11 | h11 | h11) <;> 
        simp [pow_two, Int.mul_emod, h11, Int.add_emod, Int.sub_emod] at h1 <;> omega
    assumption
  have eq6 : ∃ k : ℤ, y = 5 * k := by
    have : y % 5 = 0 := eq4
    refine' ⟨y / 5, by omega⟩
  rcases eq6 with ⟨k, hk⟩
  have eq7 : ∃ j : ℤ, x = 5 * j := by
    have : x % 5 = 0 := eq5
    refine' ⟨x / 5, by omega⟩
  rcases eq7 with ⟨j, hx⟩
  rw [hx, hk] at h
  have eq8 : 25 * (j ^ 2) = 25 * (2 * k ^ 2) - 375 * k + 5 := by
    nlinarith
  omega