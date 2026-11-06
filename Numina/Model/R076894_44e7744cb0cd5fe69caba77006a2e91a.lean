import Mathlib

theorem number_theory_121372 (a : ℤ) : ¬ 289 ∣ a^2 - 3 * a - 19 := by
  intro h
  have h2 : (a^2 - 3 * a - 19) % 289 = 0 := by
    omega
  have h3 : (a^2 - 3 * a - 19) % 17 = 0 := by
    omega
  have h4 : a % 17 = 10 := by
    have h17 : a % 17 = 0 ∨ a % 17 = 1 ∨ a % 17 = 2 ∨ a % 17 = 3 ∨ a % 17 = 4 ∨ a % 17 = 5 ∨ a % 17 = 6 ∨ a % 17 = 7 ∨ a % 17 = 8 ∨ a % 17 = 9 ∨ a % 17 = 10 ∨ a % 17 = 11 ∨ a % 17 = 12 ∨ a % 17 = 13 ∨ a % 17 = 14 ∨ a % 17 = 15 ∨ a % 17 = 16 := by
      omega
    rcases h17 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h] at h3 <;> tauto
  have h5 : a % 289 = 10 ∨ a % 289 = 27 ∨ a % 289 = 44 ∨ a % 289 = 61 ∨ a % 289 = 78 ∨ a % 289 = 95 ∨ a % 289 = 112 ∨ a % 289 = 129 ∨ a % 289 = 146 ∨ a % 289 = 163 ∨ a % 289 = 180 ∨ a % 289 = 197 ∨ a % 289 = 214 ∨ a % 289 = 231 ∨ a % 289 = 248 ∨ a % 289 = 265 ∨ a % 289 = 282 := by
    omega
  rcases h5 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h] at h2 <;> all_goals omega