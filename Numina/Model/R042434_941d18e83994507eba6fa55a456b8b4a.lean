import Mathlib

theorem number_theory_225738 (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    (3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c) ∧ (4 ∣ a ∨ 4 ∣ b ∨ 4 ∣ c) ∧ (5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c) := by
  constructor
  · -- Show that at least one of a, b, c is divisible by 3
    by_contra h3
    push_neg at h3
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    have h2 : b % 3 = 1 ∨ b % 3 = 2 := by
      omega
    have h3' : c % 3 = 1 ∨ c % 3 = 2 := by
      omega
    have h4 : a ^ 2 % 3 = 1 := by
      rcases h1 with (h1 | h1)
      · -- Case a % 3 = 1
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      · -- Case a % 3 = 2
        simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h5 : b ^ 2 % 3 = 1 := by
      rcases h2 with (h2 | h2)
      · -- Case b % 3 = 1
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      · -- Case b % 3 = 2
        simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h6 : c ^ 2 % 3 = 1 := by
      rcases h3' with (h3' | h3')
      · -- Case c % 3 = 1
        simp [pow_two, Int.add_emod, Int.mul_emod, h3']
      · -- Case c % 3 = 2
        simp [pow_two, Int.add_emod, Int.mul_emod, h3']
    omega
  constructor
  · -- Show that at least one of a, b, c is divisible by 4
    by_contra h4
    push_neg at h4
    have h1 : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    have h2 : b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
      omega
    have h3 : c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
      omega
    have h4 : a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h5 : b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h6 : c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h3]
    omega
  · -- Show that at least one of a, b, c is divisible by 5
    by_contra h5
    push_neg at h5
    have h1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    have h2 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
      omega
    have h3 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
      omega
    have h4 : a ^ 2 % 5 = 1 ∨ a ^ 2 % 5 = 4 := by
      rcases h1 with (h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h5 : b ^ 2 % 5 = 1 ∨ b ^ 2 % 5 = 4 := by
      rcases h2 with (h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h6 : c ^ 2 % 5 = 1 ∨ c ^ 2 % 5 = 4 := by
      rcases h3 with (h3 | h3 | h3 | h3) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h3]
    omega