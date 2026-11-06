import Mathlib

theorem number_theory_173258 (a b c : ℕ) (h₀ : a ≥ b ∧ b ≥ c) :
    3 ∣ a + b + c ∨ 3 ∣ a - b ∨ 3 ∣ b - c ∨ 3 ∣ a - c := by 
  have h1 : a ≥ b := h₀.left
  have h2 : b ≥ c := h₀.right
  have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    omega
  have h4 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  have h5 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by
    omega
  rcases h3 with (h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5) <;> 
    ( 
      simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, 
        h3, h4, h5, Nat.sub_mod_eq_zero_of_mod_eq]
      <;> omega 
      <;> try { tauto }
    )
  all_goals omega 
  <;> try { tauto }