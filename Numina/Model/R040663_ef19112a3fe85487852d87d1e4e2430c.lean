import Mathlib

theorem number_theory_174131 :
    IsLeast {n | 0 < n ∧ 26 ∣ n ∧ (n % 100 = 26) ∧ (Nat.digits 10 n).sum = 26} 46826 := by
  constructor
  · -- Show 46826 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · native_decide
  · -- Show no smaller element is in the set
    intro n ⟨hn_pos, hn_div, hnend, hsum⟩
    by_contra h
    push_neg at h
    have h1 : n < 46826 := h
    have h2 : n % 26 = 0 := by
      exact Nat.dvd_iff_mod_eq_zero.mp hn_div
    have h3 : n % 100 = 26 := hnend
    have h4 : ∃ k, n = 100 * k + 26 := by
      refine' ⟨n / 100, by omega⟩
    rcases h4 with ⟨k, hk⟩
    have h5 : (100 * k + 26) % 26 = 0 := by
      rw [show n = 100 * k + 26 by exact_mod_cast hk] at h2
      exact h2
    have h_k : k % 13 = 0 := by
      omega
    have h6 : ∃ m, k = 13 * m := by
      refine' ⟨k / 13, by omega⟩
    rcases h6 with ⟨m, hm⟩
    have h_n : n = 1300 * m + 26 := by
      rw [show n = 100 * k + 26 by exact_mod_cast hk]
      rw [show k = 13 * m by exact_mod_cast hm]
      all_goals omega
    have h7 : m < 36 := by
      by_contra h8
      push_neg at h8
      have h9 : n ≥ 1300 * 36 + 26 := by
        rw [h_n]
        omega
      norm_num at h9
      omega
    interval_cases m <;> norm_num [h_n] at hsum h1 h2 h3
    <;> try { contradiction }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { nlinarith }