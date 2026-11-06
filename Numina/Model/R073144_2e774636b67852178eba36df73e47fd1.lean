import Mathlib

theorem number_theory_4107 :
    IsGreatest {n : ℕ | 0 < n ∧ 12^n ∣ Nat.factorial 36} 17 := by 
  constructor
  · -- 证明17属于集合
    constructor
    · norm_num 
    native_decide
  · -- 证明对于任意n属于集合，n ≤ 17
    intro n hn
    have ⟨hn_pos, hn_div⟩ := hn
    by_contra h
    push_neg at h
    have h1 : n ≥ 18 := by linarith
    have h2 : ¬(12 ^ 18 ∣ Nat.factorial 36) := by 
      native_decide
    have h3 : 12 ^ 18 ∣ 12 ^ n := by 
      exact pow_dvd_pow _ (by linarith)
    have h4 : 12 ^ 18 ∣ Nat.factorial 36 := by 
      exact dvd_trans h3 hn_div
    exact h2 h4