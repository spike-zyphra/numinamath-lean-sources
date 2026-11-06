import Mathlib

theorem number_theory_260875 (a b c : ℤ) (h : a^2 + b^2 = c^2) :
    7 ∣ (a^2 - b^2) ∨ 7 ∣ (a^2 - c^2) ∨ 7 ∣ (b^2 - c^2) := by
  by_contra h1
  push_neg at h1 
  have h2 : a^2 % 7 = 0 ∨ a^2 % 7 = 1 ∨ a^2 % 7 = 2 ∨ a^2 % 7 = 4 := by
    have h1 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]
  have h3 : b^2 % 7 = 0 ∨ b^2 % 7 = 1 ∨ b^2 % 7 = 2 ∨ b^2 % 7 = 4 := by
    have h1 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]
  have h4 : c^2 % 7 = 0 ∨ c^2 % 7 = 1 ∨ c^2 % 7 = 2 ∨ c^2 % 7 = 4 := by
    have h1 : c % 7 = 0 ∨ c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1]
  have h5 : a^2 % 7 ≠ b^2 % 7 := by
    omega
  -- $a^2 \not\equiv c^2 \pmod{7}$
  have h6 : a^2 % 7 ≠ c^2 % 7 := by
    omega
  -- $b^2 \not\equiv c^2 \pmod{7}$
  have h7 : b^2 % 7 ≠ c^2 % 7 := by
    omega
  omega