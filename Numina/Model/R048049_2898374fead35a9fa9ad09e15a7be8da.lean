import Mathlib

theorem number_theory_71218 :
    IsLeast {t : ℕ | 0 < t ∧ ∃ x : Fin t → ℤ, ∑ i : Fin t, (x i)^3 = 2002^2002} 4 := by
  constructor
  · -- Show that 4 belongs to the set
    constructor
    · norm_num
    · -- To express 2002^2002 as the sum of 4 cubes
      use (fun i =>
        match i with
        | 0 | 1 => 10 * 2002 ^ 667
        | 2 | 3 => 1 * 2002 ^ 667
        | _ => 0
      )
      native_decide
  · -- Now, we need to show minimality - that 3 does not work
    intro t ht
    rcases ht with ⟨ht_pos, ht_exists⟩
    by_contra h
    push_neg at h
    have h1 : t < 4 := by linarith
    rcases ht_exists with ⟨x, hx⟩
    interval_cases t <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx <;> 
      norm_num at hx <;> 
      try { 
        have h1 : x 0 ^ 3 % 9 = 0 ∨ x 0 ^ 3 % 9 = 1 ∨ x 0 ^ 3 % 9 = 8 := by
          have h2 : x 0 % 9 = 0 ∨ x 0 % 9 = 1 ∨ x 0 % 9 = 2 ∨ x 0 % 9 = 3 ∨ x 0 % 9 = 4 ∨ x 0 % 9 = 5 ∨ x 0 % 9 = 6 ∨ x 0 % 9 = 7 ∨ x 0 % 9 = 8 := by 
            omega
          rcases h2 with (h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
        have h2 : x 1 ^ 3 % 9 = 0 ∨ x 1 ^ 3 % 9 = 1 ∨ x 1 ^ 3 % 9 = 8 := by
          have h2 : x 1 % 9 = 0 ∨ x 1 % 9 = 1 ∨ x 1 % 9 = 2 ∨ x 1 % 9 = 3 ∨ x 1 % 9 = 4 ∨ x 1 % 9 = 5 ∨ x 1 % 9 = 6 ∨ x 1 % 9 = 7 ∨ x 1 % 9 = 8 := by 
            omega
          rcases h2 with (h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
        have h3 : x 2 ^ 3 % 9 = 0 ∨ x 2 ^ 3 % 9 = 1 ∨ x 2 ^ 3 % 9 = 8 := by
          have h2 : x 2 % 9 = 0 ∨ x 2 % 9 = 1 ∨ x 2 % 9 = 2 ∨ x 2 % 9 = 3 ∨ x 2 % 9 = 4 ∨ x 2 % 9 = 5 ∨ x 2 % 9 = 6 ∨ x 2 % 9 = 7 ∨ x 2 % 9 = 8 := by 
            omega
          rcases h2 with (h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
        omega
      }