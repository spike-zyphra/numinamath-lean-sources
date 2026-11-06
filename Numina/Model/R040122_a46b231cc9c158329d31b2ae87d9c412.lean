import Mathlib

theorem number_theory_106637 :
    ¬∃ n : ℕ, ∃ k : ℕ, (n ^ 5 - 5 * n ^ 3 + 4 * n + 7) = k ^ 2 := by
  rintro ⟨n, ⟨k, hk⟩⟩
  have h1 : n ^ 5 - 5 * n ^ 3 + 4 * n + 7 = k ^ 2 := by 
    omega 
  have h2 : k ^ 2 % 4 = 0 ∨ k ^ 2 % 4 = 1 := by 
    have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by 
      omega 
    rcases h with (h | h | h | h)
    · -- k % 4 = 0
      simp [h, Nat.pow_mod]
      all_goals omega 
    · -- k % 4 = 1
      simp [h, Nat.pow_mod]
      all_goals omega 
    · -- k % 4 = 2
      simp [h, Nat.pow_mod]
      all_goals omega 
    · -- k % 4 = 3
      simp [h, Nat.pow_mod]
      all_goals omega 
  have h3 : (n ^ 5 - 5 * n ^ 3 + 4 * n + 7) % 4 = 3 := by 
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4)
    · -- n % 4 = 0 
      simp [h4, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.sub_mod_eq_zero_of_mod_eq, show n ^ 5 % 4 = 0 by simp [h4, Nat.pow_mod], show 5 * n ^ 3 % 4 = 0 by simp [h4, Nat.pow_mod, Nat.mul_mod], show (4 * n) % 4 = 0 by simp [h4, Nat.mul_mod] ] at *
      all_goals omega 
    · -- n % 4 = 1 
      simp [h4, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.sub_mod_eq_zero_of_mod_eq, show n ^ 5 % 4 = 1 by simp [h4, Nat.pow_mod], show 5 * n ^ 3 % 4 = 1 by simp [h4, Nat.pow_mod, Nat.mul_mod], show (4 * n) % 4 = 0 by simp [h4, Nat.mul_mod] ] at *
      all_goals omega 
    · -- n % 4 = 2 
      simp [h4, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.sub_mod_eq_zero_of_mod_eq, show n ^ 5 % 4 = 0 by simp [h4, Nat.pow_mod], show 5 * n ^ 3 % 4 = 0 by simp [h4, Nat.pow_mod, Nat.mul_mod], show (4 * n) % 4 = 0 by simp [h4, Nat.mul_mod] ] at *
      all_goals omega 
    · -- n % 4 = 3
      simp [h4, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.sub_mod_eq_zero_of_mod_eq, show n ^ 5 % 4 = 3 by simp [h4, Nat.pow_mod], show 5 * n ^ 3 % 4 = 3 by simp [h4, Nat.pow_mod, Nat.mul_mod], show (4 * n) % 4 = 0 by simp [h4, Nat.mul_mod] ] at *
      all_goals omega 
  have h5 : k ^ 2 % 4 = 3 := by 
    omega 
  omega 
  all_goals omega 
  all_goals ring_nf at h1 
  all_goals omega 
  <;> omega 
  <;> tauto 
  all_goals tauto