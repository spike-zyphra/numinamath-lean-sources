import Mathlib

theorem algebra_140289 (a b c : ℤ) :
    ∃ n : ℤ, n > 0 ∧ ¬(IsSquare (n^3 + a * n^2 + b * n + c)) := by
  by_cases h1 : (1 + a + b + c) % 4 = 2 ∨ (1 + a + b + c) % 4 = 3
  · -- If 1 + a + b + c ≡ 2 or 3 [MOD 4], then n = 1 works
    use 1
    constructor
    · norm_num
    · -- Show that 1 + a + b + c is not a perfect square
      intro h
      rcases h with ⟨k, hk⟩
      have h2 : k ^ 2 = 1 + a + b + c := by
        nlinarith
      have h3 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by
        have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
          omega
        rcases h4 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      have h4 : k ^ 2 % 4 = 2 ∨ k ^ 2 % 4 = 3 := by
        omega
      omega
  · -- If not, check n = 2
    by_cases h2 : (2 * b + c) % 4 = 2 ∨ (2 * b + c) % 4 = 3
    · -- If 2b + c ≡ 2 or 3 [MOD 4], then n = 2 works
      use 2
      constructor
      · norm_num
      · -- Show that 8 + 4a + 2b + c is not a perfect square
        intro h
        rcases h with ⟨k, hk⟩
        have h2 : k ^ 2 = 8 + 4 * a + 2 * b + c := by
          nlinarith
        have h3 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by
          have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
            omega
          rcases h4 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
        have h4 : k ^ 2 % 4 = 2 ∨ k ^ 2 % 4 = 3 := by
          have eq1 : (8 + 4 * a + 2 * b + c) % 4 = (2 * b + c) % 4 := by
            omega
          have eq2 : k ^ 2 % 4 = (2 * b + c) % 4 := by
            omega
          omega
        omega
    · -- If not, check n = 3
      by_cases h3 : (3 + a + 3 * b + c) % 4 = 2 ∨ (3 + a + 3 * b + c) % 4 = 3
      · -- If 3 + a + 3b + c ≡ 2 or 3 [MOD 4], then n = 3 works
        use 3
        constructor
        · norm_num
        · -- Show that 27 + 9a + 3b + c is not a perfect square
          intro h
          rcases h with ⟨k, hk⟩
          have h2 : k ^ 2 = 27 + 9 * a + 3 * b + c := by
            nlinarith
          have h3 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by
            have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
              omega
            rcases h4 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
          have h4 : k ^ 2 % 4 = 2 ∨ k ^ 2 % 4 = 3 := by
            have eq1 : (27 + 9 * a + 3 * b + c) % 4 = (3 + a + 3 * b + c) % 4 := by
              omega
            have eq2 : k ^ 2 % 4 = (3 + a + 3 * b + c) % 4 := by
              omega
            omega
          omega
      · -- If not, check n = 4
        have h4 : (c) % 4 = 2 ∨ (c) % 4 = 3 := by
          omega
        use 4
        constructor
        · norm_num
        · -- Show that 64 + 16a + 4b + c is not a perfect square
          intro h
          rcases h with ⟨k, hk⟩
          have h2 : k ^ 2 = 64 + 16 * a + 4 * b + c := by
            nlinarith
          have h3 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by
            have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
              omega
            rcases h4 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
          have h4 : k ^ 2 % 4 = 2 ∨ k ^ 2 % 4 = 3 := by
            have eq1 : (64 + 16 * a + 4 * b + c) % 4 = (c) % 4 := by
              omega
            have eq2 : k ^ 2 % 4 = (c) % 4 := by
              omega
            omega
          omega