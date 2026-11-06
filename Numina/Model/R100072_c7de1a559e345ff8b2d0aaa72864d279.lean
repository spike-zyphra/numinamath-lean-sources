import Mathlib

theorem number_theory_8138 :
    IsLeast {k | ∃ m n, m > n ∧ n ≥ 1 ∧ m + n = k ∧ 1000 ∣ 1978 ^ m - 1978 ^ n} 106 := by 
  constructor
  · -- Show 106 is in the set
    use 103, 3
    all_goals norm_num
  · -- Prove minimality of 106
    rintro k ⟨m, n, hmn, hn, hm, hk⟩
    have h1 : m > n := hmn
    have h2 : n ≥ 1 := hn
    have h3 : m + n = k := hm
    have h4 : 1000 ∣ 1978 ^ m - 1978 ^ n := hk
    by_contra h
    push_neg at h
    have h5 : m + n < 106 := by linarith [h3, h]
    have h6 : m ≤ 104 := by omega
    have h7 : n ≤ 103 := by omega
    interval_cases m <;> interval_cases n
    <;> norm_num at h4 <;> omega