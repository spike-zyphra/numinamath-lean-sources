import Mathlib

theorem number_theory_12410 (x y : ℤ) (hx : 7 ∣ x - 3) (hy : 7 ∣ y + 3) :
    IsLeast {n | 0 < n ∧ 7 ∣ x ^ 2 + x * y + y ^ 2 + n} 5 := by

  have hx1 : x % 7 = 3 := by 
    omega

  have hy1 : y % 7 = 4 := by 
    omega

  constructor
  · -- Show that 5 is indeed in the set.
    constructor
    · norm_num
    · -- Show that 7 divides 5 + x^2 + x * y + y^2
      have h1 : (x ^ 2 + x * y + y ^ 2 + 5) % 7 = 0 := by
        have hx2 : x % 7 = 3 := hx1
        have hy2 : y % 7 = 4 := hy1
        simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, hx2, hy2]
        <;> omega
      have h2 : 7 ∣ x ^ 2 + x * y + y ^ 2 + 5 := by
        omega
      exact h2
  · -- Show that 5 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : (x ^ 2 + x * y + y ^ 2) % 7 = 2 := by
      have hx2 : x % 7 = 3 := hx1
      have hy2 : y % 7 = 4 := hy1
      simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, hx2, hy2]
      <;> omega
    have h3 : (x ^ 2 + x * y + y ^ 2 + n) % 7 = 0 := by 
      omega
    have h2 : n < 5 := by omega
    interval_cases n <;> omega