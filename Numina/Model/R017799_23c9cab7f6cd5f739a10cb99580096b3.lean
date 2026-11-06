import Mathlib

theorem number_theory_6277 :
    ¬∃ (x y z : ℤ), 9 ∣ x^3 + y^3 + z^3 ∧ ¬(3 ∣ x * y * z) := by
  rintro ⟨x, y, z, hdiv, hn⟩
  have h1 : ¬ (3 ∣ x) := by
    by_contra h2
    have h2' : 3 ∣ x := h2
    have h3 : 3 ∣ x * y * z := by
      have h4 : 3 ∣ x := h2'
      have h5 : 3 ∣ x * y * z := by
        have h6 : x * y * z = x * (y * z) := by ring
        rw [h6]
        apply dvd_mul_of_dvd_left
        exact h4
      assumption
    tauto
  have h2 : ¬ (3 ∣ y) := by
    by_contra h2
    have h2' : 3 ∣ y := h2
    have h3 : 3 ∣ x * y * z := by
      have h4 : 3 ∣ y := h2'
      have h5 : 3 ∣ x * y * z := by
        have h6 : x * y * z = y * (x * z) := by ring
        rw [h6]
        apply dvd_mul_of_dvd_left
        exact h4
      assumption
    tauto
  have h3 : ¬ (3 ∣ z) := by
    by_contra h2
    have h2' : 3 ∣ z := h2
    have h3 : 3 ∣ x * y * z := by
      have h4 : 3 ∣ z := h2'
      have h5 : 3 ∣ x * y * z := by
        have h6 : x * y * z = z * (x * y) := by ring
        rw [h6]
        apply dvd_mul_of_dvd_left
        exact h4
      assumption
    tauto
  have hx3 : x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
    have h8 : x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
      omega
    rcases h8 with (h | h | h | h | h | h)
    · -- x ≡ 1 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- x ≡ 2 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- x ≡ 4 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- x ≡ 5 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- x ≡ 7 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- x ≡ 8 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
  have hy3 : y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by 
    have h8 : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
      omega
    rcases h8 with (h | h | h | h | h | h)
    · -- y ≡ 1 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- y ≡ 2 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- y ≡ 4 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- y ≡ 5 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- y ≡ 7 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- y ≡ 8 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
  have hz3 : z^3 % 9 = 1 ∨ z^3 % 9 = 8 := by 
    have h8 : z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 7 ∨ z % 9 = 8 := by 
      omega
    rcases h8 with (h | h | h | h | h | h)
    · -- z ≡ 1 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- z ≡ 2 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- z ≡ 4 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- z ≡ 5 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- z ≡ 7 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    · -- z ≡ 8 (mod 9)
      norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
  omega