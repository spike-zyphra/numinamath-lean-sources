import Mathlib

theorem number_theory_188725 (n : ℕ) (h₀ : Odd n) :
    24 ∣ n^3 - n := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := h₀
    omega
  have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h5 : n % 2 = 1 := h1
    omega
  have h3 : (n ^ 3) % 8 = n % 8 := by
    rcases h2 with (h | h | h | h) <;> norm_num [h, Nat.pow_mod]
  have h4 : (n ^ 3) % 3 = n % 3 := by
    have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h5 with (h | h | h) <;> norm_num [h, Nat.pow_mod]
  have h5 : (n ^ 3 - n) % 8 = 0 := by
    omega
  have h6 : (n ^ 3 - n) % 3 = 0 := by
    omega
  have h7 : 24 ∣ n^3 - n := by
    omega
  exact h7