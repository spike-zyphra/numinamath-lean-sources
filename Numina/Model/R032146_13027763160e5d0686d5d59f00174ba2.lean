import Mathlib

theorem Other_5738 (n : ℤ) :
  ¬ ∃ x, x^3 = 3 * n^2 + 3 * n + 7 := by
  intro h
  rcases h with ⟨x, hx⟩
  have h1 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
    have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_succ, h1, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : (3 * n^2 + 3 * n + 7) % 9 = 4 ∨ (3 * n^2 + 3 * n + 7) % 9 = 7 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with (h3 | h3 | h3)
    · -- n ≡ 0
      have h4 : n % 3 = 0 := h3
      have h5 : n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6 := by
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- n ≡ 0 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 3 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 6 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
    · -- n ≡ 1
      have h4 : n % 3 = 1 := h3
      have h5 : n % 9 = 1 ∨ n % 9 = 4 ∨ n % 9 = 7 := by
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- n ≡ 1 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 4 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 7 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
    · -- n ≡ 2
      have h4 : n % 3 = 2 := h3
      have h5 : n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 8 := by
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- n ≡ 2 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 5 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
      · -- n ≡ 8 (mod 9)
        simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h5]
  have h3 : x^3 % 9 = (3 * n^2 + 3 * n + 7) % 9 := by
    omega
  omega