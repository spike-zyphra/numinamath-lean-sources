import Mathlib

theorem number_theory_73358 :
    ¬∃ x y z : ℤ, 3 * x ^ 2 + 4 * y ^ 2 - 5 * z ^ 2 = 10 := by
  rintro ⟨x, y, z, h⟩
  have h1 : (3 * x ^ 2 + 4 * y ^ 2) % 5 = 0 := by
    have h2 : (3 * x ^ 2 + 4 * y ^ 2 - 5 * z ^ 2) % 5 = 0 := by
      omega
    omega
  have h2 : x % 5 = 0 := by
    have h3 : (3 * x ^ 2 + 4 * y ^ 2) % 5 = 0 := h1
    have h4 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    have h5 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h4, h5] at h3 
    <;> omega
  have h3 : y % 5 = 0 := by
    have h3 : (3 * x ^ 2 + 4 * y ^ 2) % 5 = 0 := h1
    have h4 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    have h5 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h4, h5] at h3 
    <;> omega
  -- Therefore x and y must be multiples of 5.
  have h4 : ∃ k : ℤ, x = 5 * k := by
    refine' ⟨x / 5, by omega⟩
  have h5 : ∃ l : ℤ, y = 5 * l := by
    refine' ⟨y / 5, by omega⟩
  rcases h4 with ⟨k, hk⟩
  rcases h5 with ⟨l, hl⟩
  rw [hk] at h
  rw [hl] at h
  have h2 : (15 * k ^ 2 + 20 * l ^ 2 - z ^ 2) = 2 := by
    nlinarith
  have h3 : z ^ 2 % 5 = 0 ∨ z ^ 2 % 5 = 1 ∨ z ^ 2 % 5 = 4 := by
    have h4 : z % 5 = 0 ∨ z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    <;> omega
  have h4 : z ^ 2 % 5 = 3 := by
    omega
  omega