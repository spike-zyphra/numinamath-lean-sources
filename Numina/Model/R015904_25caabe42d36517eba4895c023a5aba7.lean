import Mathlib

theorem algebra_279 : IsLeast {m : ℤ | m > 0 ∧ ∃a b : ℤ, a > 0 ∧ b > 0 ∧ m = 3 * a ^ 2 - a * b ^ 2 - 2 * b - 4} 2 := by 
  constructor
  · -- Show 2 is in the set
    constructor
    · norm_num
    · -- Find specific a, b such that M = 2
      use 4, 3
      all_goals norm_num
  · -- Show 2 is the minimum
    intro m hm
    rcases hm with ⟨hm_pos, a, b, ha_pos, hb_pos, hm_eq⟩
    by_contra h
    push_neg at h
    have h1 : m = 1 := by
      omega
    rw [h1] at hm_eq
    have h_eq : 3 * a ^ 2 - a * b ^ 2 - 2 * b - 4 = 1 := by
      linarith 
    have h_eq_mod_4 : (3 * a ^ 2 - a * b ^ 2 - 2 * b - 4) % 4 = 1 % 4 := by
      omega 
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
      omega
    have h3 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> simp [Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, h2, h3, Int.sub_emod, Int.add_emod, Int.mul_emod] at h_eq_mod_4 <;> omega