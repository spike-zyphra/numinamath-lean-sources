import Mathlib

/-
8.47 Let $a, b, c$ be the side lengths of a right triangle. Prove that if these numbers are all integers, then the product $abc$ is divisible by 30.
(Spanish Mathematics Competition, 1992)
-/

theorem number_theory_241211 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) : 30 ∣ a * b * c := by

  have h1 : a % 2 = 0 ∨ b % 2 = 0 ∨ c % 2 = 0 := by
    by_contra h
    push_neg at h
    have ha : a % 2 = 1 := by omega
    have hb : b % 2 = 1 := by omega
    have hc : c % 2 = 1 := by omega
    have h1 : a^2 % 4 = 1 := by
      have h1 : a % 4 = 1 ∨ a % 4 = 3 := by omega
      rcases h1 with (h1 | h1)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h2 : b^2 % 4 = 1 := by
      have h2 : b % 4 = 1 ∨ b % 4 = 3 := by omega
      rcases h2 with (h2 | h2)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h3 : (a^2 + b^2) % 4 = 2 := by omega
    have h4 : c^2 % 4 = 1 := by
      have h4 : c % 4 = 1 ∨ c % 4 = 3 := by omega
      rcases h4 with (h4 | h4)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h4]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h4]
    have h5 : (a^2 + b^2) % 4 = c^2 % 4 := by omega
    omega

  have h2 : a % 3 = 0 ∨ b % 3 = 0 ∨ c % 3 = 0 := by
    by_contra h
    push_neg at h
    have ha : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hb : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have hc : c % 3 = 1 ∨ c % 3 = 2 := by omega
    have h1 : a^2 % 3 = 1 := by
      rcases ha with (h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h2 : b^2 % 3 = 1 := by
      rcases hb with (h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h3 : (a^2 + b^2) % 3 = 2 := by omega
    have h4 : c^2 % 3 = 1 := by
      rcases hc with (h | h)
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
      · norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h5 : (a^2 + b^2) % 3 = c^2 % 3 := by omega
    omega

  have h3 : a % 5 = 0 ∨ b % 5 = 0 ∨ c % 5 = 0 := by
    by_contra h
    push_neg at h
    have ha : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    have hb : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
    have hc : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by omega
    have h1 : a^2 % 5 = 1 ∨ a^2 % 5 = 4 := by
      rcases ha with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h2 : b^2 % 5 = 1 ∨ b^2 % 5 = 4 := by
      rcases hb with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h3 : c^2 % 5 = 1 ∨ c^2 % 5 = 4 := by
      rcases hc with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
    have h4 : (a^2 + b^2) % 5 = 0 ∨ (a^2 + b^2) % 5 = 2 ∨ (a^2 + b^2) % 5 = 3 := by
      rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> omega
    have h5 : (a^2 + b^2) % 5 = c^2 % 5 := by omega
    rcases h4 with (h4 | h4 | h4) <;> rcases h3 with (h3 | h3) <;> omega

  have h4 : (a * b * c) % 2 = 0 := by
    rcases h1 with (h | h | h)
    · -- a % 2 = 0
      simp [Int.mul_emod, h]
    · -- b % 2 = 0
      simp [Int.mul_emod, h]
    · -- c % 2 = 0
      simp [Int.mul_emod, h]

  have h5 : (a * b * c) % 3 = 0 := by
    rcases h2 with (h | h | h)
    · -- a % 3 = 0
      simp [Int.mul_emod, h]
    · -- b % 3 = 0
      simp [Int.mul_emod, h]
    · -- c % 3 = 0
      simp [Int.mul_emod, h]

  have h6 : (a * b * c) % 5 = 0 := by
    rcases h3 with (h | h | h)
    · -- a % 5 = 0
      simp [Int.mul_emod, h]
    · -- b % 5 = 0
      simp [Int.mul_emod, h]
    · -- c % 5 = 0
      simp [Int.mul_emod, h]
      
  omega