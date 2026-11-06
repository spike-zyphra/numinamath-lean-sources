import Mathlib

theorem number_theory_144544 : IsGreatest {x | ∀ a b c d : ℤ, x ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c)} 12 := by
  constructor
  · -- Show 12 is indeed in the set
    intro a b c d
    have h1 : (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) % 12 = 0 := by
      have h2 : (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) % 4 = 0 := by
        have h2a : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        have h2b : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        have h2c : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        have h2d : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
        rcases h2a with (h2a | h2a | h2a | h2a) <;> rcases h2b with (h2b | h2b | h2b | h2b) <;> rcases h2c with (h2c | h2c | h2c | h2c) <;> rcases h2d with (h2d | h2d | h2d | h2d) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h2a, h2b, h2c, h2d]
      have h3 : (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) % 3 = 0 := by
        have h3a : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
        have h3b : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
        have h3c : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
        have h3d : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
        rcases h3a with (h3a | h3a | h3a) <;> rcases h3b with (h3b | h3b | h3b) <;> rcases h3c with (h3c | h3c | h3c) <;> rcases h3d with (h3d | h3d | h3d) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, h3a, h3b, h3c, h3d]
      omega
    exact Int.dvd_of_emod_eq_zero h1
  · -- Show no integer greater than 12 is in the set
    intro x hx
    have h2 : ∀ a b c d : ℤ, x ∣ (a - b) * (b - c) * (c - d) * (d - a) * (b - d) * (a - c) := hx
    have h3 := h2 0 1 2 3
    norm_num at h3
    have h12 : x ∣ 12 := h3
    have h6 : x ≤ 12 := by
      apply Int.le_of_dvd (show 0 < 12 by norm_num) h12
    linarith