import Mathlib

theorem number_theory_68648 (a b : ℤ) :
    a % 2 = b % 2 ↔ ∃ c d : ℤ, a^2 + b^2 + c^2 + 1 = d^2 := by 
  constructor
  · -- Assume a % 2 = b % 2, prove ∃ c d : ℤ, a^2 + b^2 + c^2 + 1 = d^2
    intro h 
    have h1 : (a + b) % 2 = 0 := by
      omega 
    have h2 : (a ^ 2 + b ^ 2) % 2 = 0 := by
      have ha1 : a % 2 = 0 ∨ a % 2 = 1 := by 
        omega 
      have hb1 : b % 2 = 0 ∨ b % 2 = 1 := by 
        omega 
      rcases ha1 with (h11 | h11)
      · -- a is even
        rcases hb1 with (h12 | h12)
        · -- b is even
          simp [pow_two, Int.add_emod, Int.mul_emod, h11, h12] 
        · -- b is odd
          exfalso 
          omega 
      · -- a is odd
        rcases hb1 with (h12 | h12)
        · -- b is even
          exfalso 
          omega 
        · -- b is odd
          simp [pow_two, Int.add_emod, Int.mul_emod, h11, h12] 
    have h3 : ∃ k : ℤ, a ^ 2 + b ^ 2 = 2 * k := by 
      have h4 : (a ^ 2 + b ^ 2) % 2 = 0 := h2
      refine' ⟨(a ^ 2 + b ^ 2) / 2, by 
        omega 
      ⟩ 
    rcases h3 with ⟨k, hk⟩
    use k 
    use k + 1 
    nlinarith [hk]
  · -- Assume ∃ c d : ℤ, a^2 + b^2 + c^2 + 1 = d^2, prove a % 2 = b % 2 
    rintro ⟨c, d, heq⟩ 
    by_contra h 
    push_neg at h 
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
      omega 
    have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega 
    have h3 : a % 2 ≠ b % 2 := h 
    have h4 : (a ^ 2 : ℤ) % 2 = a % 2 := by 
      have h11 : a % 2 = 0 ∨ a % 2 = 1 := by 
        omega 
      rcases h11 with (h11 | h11)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h11] 
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h11] 
    have h5 : (b ^ 2 : ℤ) % 2 = b % 2 := by 
      have h11 : b % 2 = 0 ∨ b % 2 = 1 := by 
        omega 
      rcases h11 with (h11 | h11)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h11] 
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h11] 
    have h7 : (a ^ 2 : ℤ) % 8 = 0 ∨ (a ^ 2 : ℤ) % 8 = 1 ∨ (a ^ 2 : ℤ) % 8 = 4 := by
      have h11 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
        omega 
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h11]
    have h8 : (b ^ 2 : ℤ) % 8 = 0 ∨ (b ^ 2 : ℤ) % 8 = 1 ∨ (b ^ 2 : ℤ) % 8 = 4 := by 
      have h11 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
        omega 
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h11]
    have h9 : (c ^ 2 : ℤ) % 8 = 0 ∨ (c ^ 2 : ℤ) % 8 = 1 ∨ (c ^ 2 : ℤ) % 8 = 4 := by 
      have h11 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
        omega 
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h11]
    have h10 : (d ^ 2 : ℤ) % 8 = 0 ∨ (d ^ 2 : ℤ) % 8 = 1 ∨ (d ^ 2 : ℤ) % 8 = 4 := by 
      have h11 : d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 2 ∨ d % 8 = 3 ∨ d % 8 = 4 ∨ d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7 := by 
        omega 
      rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h11]
    have h11 : (a^2 + b^2 + c^2 + 1 : ℤ) % 8 = (d^2 : ℤ) % 8 := by 
      omega 
    omega