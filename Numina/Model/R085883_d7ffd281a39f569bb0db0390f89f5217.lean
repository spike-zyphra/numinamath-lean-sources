import Mathlib

theorem number_theory_19594 :
    IsLeast {x | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ¬(3 ∣ a) ∧ ¬(3 ∣ b) ∧ (a ^ 2 + b ^ 2) % 3 = x} 2 := by 
  constructor
  · -- Show that 2 is achievable, using the witness (1, 1)
    use 1, 1
    all_goals norm_num
  · -- Now we need to show that for any x in the set, x >= 2
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hha, hhb, h⟩
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by 
      omega
    have h2 : b % 3 = 1 ∨ b % 3 = 2 := by 
      omega
    have h3 : a^2 % 3 = 1 := by 
      rcases h1 with (h | h)
      · norm_num [Nat.pow_mod, h]
      · norm_num [Nat.pow_mod, h]
    have h4 : b^2 % 3 = 1 := by 
      rcases h2 with (h | h)
      · norm_num [Nat.pow_mod, h]
      · norm_num [Nat.pow_mod, h]
    have h5 : (a ^ 2 + b ^ 2) % 3 = 2 := by 
      simp [Nat.add_mod, h3, h4]
    omega