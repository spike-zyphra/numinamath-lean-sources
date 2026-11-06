import Mathlib

theorem number_theory_202597 :
    ¬∃ x y : ℤ, x^2 + y^2 - 19 * x * y - 19 = 0 := by

  rintro ⟨x, y, h⟩
  have h1 : x^2 + y^2 = 19 * (x * y + 1) := by linarith
  have h2 : (x^2 + y^2 : ℤ) % 19 = 0 := by
    omega
  have h3 : x % 19 = 0 := by 
    have h4 : x % 19 = 0 ∨ x % 19 = 1 ∨ x % 19 = 2 ∨ x % 19 = 3 ∨ x % 19 = 4 ∨ x % 19 = 5 ∨ x % 19 = 6 ∨ x % 19 = 7 ∨ x % 19 = 8 ∨ x % 19 = 9 ∨ x % 19 = 10 ∨ x % 19 = 11 ∨ x % 19 = 12 ∨ x % 19 = 13 ∨ x % 19 = 14 ∨ x % 19 = 15 ∨ x % 19 = 16 ∨ x % 19 = 17 ∨ x % 19 = 18 := by 
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> ( 
      have h4' : y % 19 = 0 ∨ y % 19 = 1 ∨ y % 19 = 2 ∨ y % 19 = 3 ∨ y % 19 = 4 ∨ y % 19 = 5 ∨ y % 19 = 6 ∨ y % 19 = 7 ∨ y % 19 = 8 ∨ y % 19 = 9 ∨ y % 19 = 10 ∨ y % 19 = 11 ∨ y % 19 = 12 ∨ y % 19 = 13 ∨ y % 19 = 14 ∨ y % 19 = 15 ∨ y % 19 = 16 ∨ y % 19 = 17 ∨ y % 19 = 18 := by 
        omega 
      rcases h4' with (h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4' | h4') <;> ( 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h4, h4'] at h2 
        <;> omega 
      ) 
    )
  have h4 : y % 19 = 0 := by 
    have h4' : (x^2 + y^2 : ℤ) % 19 = 0 := h2
    have hx0 : x % 19 = 0 := h3 
    have h5 : (x : ℤ) ^ 2 % 19 = 0 := by
      simp [hx0, pow_two, Int.add_emod, Int.mul_emod]
    have h6 : (y : ℤ) ^ 2 % 19 = 0 := by 
      omega 
    have h7 : y % 19 = 0 := by 
      have h8 : y ^ 2 % 19 = 0 := h6 
      have h9 : y % 19 = 0 ∨ y % 19 = 1 ∨ y % 19 = 2 ∨ y % 19 = 3 ∨ y % 19 = 4 ∨ y % 19 = 5 ∨ y % 19 = 6 ∨ y % 19 = 7 ∨ y % 19 = 8 ∨ y % 19 = 9 ∨ y % 19 = 10 ∨ y % 19 = 11 ∨ y % 19 = 12 ∨ y % 19 = 13 ∨ y % 19 = 14 ∨ y % 19 = 15 ∨ y % 19 = 16 ∨ y % 19 = 17 ∨ y % 19 = 18 := by 
        omega 
      rcases h9 with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9) <;> ( 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h9] at h8 
        <;> omega 
      )
    assumption 
  have h5 : ∃ k : ℤ, x = 19 * k := ⟨x / 19, by omega⟩ 
  rcases h5 with ⟨k, hk⟩ 
  have h6 : ∃ l : ℤ, y = 19 * l := ⟨y / 19, by omega⟩ 
  rcases h6 with ⟨l, hl⟩ 
  rw [hk] at h1 
  rw [hl] at h1 
  have h7 : 19 * (19 * (k ^ 2 + l ^ 2) - 19 * 19 * (k * l) - 1) = 0 := by 
    nlinarith 
  have h8 : 19 * (k ^ 2 + l ^ 2) - 19 * 19 * (k * l) - 1 = 0 := by 
    linarith 
  have h9 : (19 * (k ^ 2 + l ^ 2) - 19 * 19 * (k * l) - 1 : ℤ) % 19 = 0 := by 
    omega 
  omega