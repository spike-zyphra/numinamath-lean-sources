import Mathlib

theorem number_theory_108714 : ¬ ∃ x y : ℤ, y^2 = x^5 - 4 := by
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have eq1 : y^2 % 11 = 0 ∨ y^2 % 11 = 1 ∨ y^2 % 11 = 3 ∨ y^2 % 11 = 4 ∨ y^2 % 11 = 5 ∨ y^2 % 11 = 9 := by
    have h1 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h)
    · -- y ≡ 0 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 1 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 2 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 3 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 4 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 5 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 6 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 7 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 8 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 9 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- y ≡ 10 (mod 11)
      simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have eq2 : x^5 % 11 = 0 ∨ x^5 % 11 = 1 ∨ x^5 % 11 = 10 := by
    have h1 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h)
    · -- x ≡ 0 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 1 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 2 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 3 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 4 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 5 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 6 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 7 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 8 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 9 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
    · -- x ≡ 10 (mod 11)
      simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      <;> omega
  have h1 : y^2 = x^5 - 4 := h_eq
  have h1_mod : y^2 % 11 = (x^5 - 4 : ℤ) % 11 := by
    rw [h1]
  omega