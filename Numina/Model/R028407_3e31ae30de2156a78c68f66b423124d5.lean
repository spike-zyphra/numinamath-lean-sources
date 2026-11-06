import Mathlib

theorem number_theory_208 : IsLeast {x | x > 0 ∧ ∀ n ∈ Finset.Icc 1 9, n ∣ x} 2520 := by
  constructor
  · -- First part: Show 2520 is in the set.
    constructor
    · norm_num
    · intro n hn
      fin_cases hn <;> norm_num
  · -- Second part: Show there is no smaller element in the set.
    intro x hx
    rcases hx with ⟨hx_pos, hx_div⟩
    have h1 : 1 ∣ x := hx_div 1 (by norm_num)
    have h2 : 2 ∣ x := hx_div 2 (by norm_num)
    have h3 : 3 ∣ x := hx_div 3 (by norm_num)
    have h4 : 4 ∣ x := hx_div 4 (by norm_num)
    have h5 : 5 ∣ x := hx_div 5 (by norm_num)
    have h6 : 6 ∣ x := hx_div 6 (by norm_num)
    have h7 : 7 ∣ x := hx_div 7 (by norm_num)
    have h8 : 8 ∣ x := hx_div 8 (by norm_num)
    have h9 : 9 ∣ x := hx_div 9 (by norm_num)
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 hx_pos h ⊢ <;> all_goals
      omega