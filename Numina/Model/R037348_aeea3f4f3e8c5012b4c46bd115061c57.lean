import Mathlib

theorem number_theory_16710 :
    IsGreatest {n : Nat | 0 < n ∧ ((Nat.digits 10 n).all (fun x => Even x)) ∧ n < 10000 ∧ 9 ∣ n} 8820 := by
  constructor
  · -- Show 8820 is in the set
    refine' ⟨by norm_num, by native_decide, by norm_num, by norm_num⟩
  · -- Show 8820 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_digits, hn_lt, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n > 8820 := by omega
    have h2 : n < 10000 := by omega
    interval_cases n <;> norm_num at hn_div h1 h2 ⊢ <;> norm_num [Nat.even_iff, List.all_cons] at hn_digits ⊢ <;> omega