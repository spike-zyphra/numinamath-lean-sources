import Mathlib

theorem number_theory_7744 :
    IsLeast {a : ℕ | 0 < a ∧ ∀ x, 65 ∣ (5 * x ^ 13 + 13 * x ^ 5 + 9 * a * x)} 63 := by
  constructor
  · -- Show 63 is in the set
    constructor
    · -- Show 63 is positive
      norm_num
    · -- Show that 63 is a solution
      intro x
      have h1 : (5 * x ^ 13 + 13 * x ^ 5 + 9 * (63 : ℕ) * x) % 65 = 0 := by
        have h1 : (5 * x ^ 13 + 13 * x ^ 5 + 9 * (63 : ℕ) * x) % 5 = 0 := by
          have h2 : ∀ x : ℕ, (5 * x ^ 13 + 13 * x ^ 5 + 9 * (63 : ℕ) * x) % 5 = 0 := by
            intro x
            have h3 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
            rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.add_mod, Nat.mul_mod, pow_succ, pow_zero, Nat.pow_mod]
          apply h2 x
        have h2 : (5 * x ^ 13 + 13 * x ^ 5 + 9 * (63 : ℕ) * x) % 13 = 0 := by
          have h3 : ∀ x : ℕ, (5 * x ^ 13 + 13 * x ^ 5 + 9 * (63 : ℕ) * x) % 13 = 0 := by
            intro x
            have h4 : x % 13 = 0 ∨ x % 13 = 1 ∨ x % 13 = 2 ∨ x % 13 = 3 ∨ x % 13 = 4 ∨ x % 13 = 5 ∨ x % 13 = 6 ∨ x % 13 = 7 ∨ x % 13 = 8 ∨ x % 13 = 9 ∨ x % 13 = 10 ∨ x % 13 = 11 ∨ x % 13 = 12 := by omega
            rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [h4, Nat.add_mod, Nat.mul_mod, pow_succ, pow_zero, Nat.pow_mod]
          apply h3 x
        omega
      omega
  · -- Show no smaller positive integer is in the set
    intro a ha
    rcases ha with ⟨ha_pos, ha_div⟩
    by_contra h
    push_neg at h
    have h2 := ha_div 1
    norm_num at h2
    omega