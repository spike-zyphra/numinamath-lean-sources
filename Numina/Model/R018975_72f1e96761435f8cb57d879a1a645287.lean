import Mathlib

theorem number_theory_255724 (a : Finset ℤ) (h : ∑ x ∈ a, x ≡ 0 [ZMOD 6]) :
    ∑ x ∈ a, x^3 ≡ 0 [ZMOD 6] := by 
  have h2 : ∀ x : ℤ, x ^ 3 % 6 = x % 6 := by 
    intro x 
    have h2 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2)
    all_goals
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, Int.sub_emod, h2, Int.emod_eq_emod_iff_emod_sub_eq_zero] at *
  have h3 : (∑ x in a, x^3) % 6 = (∑ x in a, x) % 6 := by 
    have h4 : ∀ x : ℤ, x ^ 3 % 6 = x % 6 := h2 
    simp_all [Finset.sum_int_mod, h4]
  have h9 : (∑ x in a, x) % 6 = 0 := by
    norm_num [Int.ModEq] at h ⊢ 
    all_goals try tauto
  have h10 : (∑ x in a, x^3) % 6 = 0 := by 
    omega
  norm_num [Int.ModEq]
  all_goals omega