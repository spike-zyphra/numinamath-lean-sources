import Mathlib

theorem number_theory_291218 (x y : ℤ) (h₀ : ∃ a, a^2 = 5 * x + 6 * y) (h₁ : ∃ b, b^2 = 6 * x + 5 * y) :
    11 ∣ x ∧ 11 ∣ y := by
  rcases h₀ with ⟨a, ha⟩
  rcases h₁ with ⟨b, hb⟩
  have h2 : a^2 + b^2 = 11 * (x + y) := by
    nlinarith [ha, hb]
  have h3 : a^2 % 11 = 0 ∨ a^2 % 11 = 1 ∨ a^2 % 11 = 3 ∨ a^2 % 11 = 4 ∨ a^2 % 11 = 5 ∨ a^2 % 11 = 9 := by
    have h : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
  have h4 : b^2 % 11 = 0 ∨ b^2 % 11 = 1 ∨ b^2 % 11 = 3 ∨ b^2 % 11 = 4 ∨ b^2 % 11 = 5 ∨ b^2 % 11 = 9 := by
    have h : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h]
  have h5 : (a^2 + b^2) % 11 = 0 := by 
    omega
  have h6 : a^2 % 11 = 0 ∧ b^2 % 11 = 0 := by
    omega
  have ha11 : 11 ∣ a := by
    by_contra h
    push_neg at h
    have h8 : a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by
      omega
    have h9 : a^2 % 11 ≠ 0 := by
      rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8) <;> norm_num [pow_two, Int.mul_emod, h8]
    omega
  have hb11 : 11 ∣ b := by
    by_contra h
    push_neg at h
    have h8 : b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by
      omega
    have h9 : b^2 % 11 ≠ 0 := by
      rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8) <;> norm_num [pow_two, Int.mul_emod, h8]
    omega
  obtain ⟨k, hk⟩ := ha11
  obtain ⟨m, hm⟩ := hb11
  have eq1 : 5 * x + 6 * y = 121 * k^2 := by 
    rw [show a = 11 * k by linarith] at ha
    linarith
  have eq2 : 6 * x + 5 * y = 121 * m^2 := by 
    rw [show b = 11 * m by linarith] at hb
    linarith
  have eq3 : 11 ∣ x := by 
    omega
  have eq4 : 11 ∣ y := by 
    omega
  exact ⟨eq3, eq4⟩