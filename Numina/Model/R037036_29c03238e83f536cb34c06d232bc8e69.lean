import Mathlib

theorem algebra_21902:
    IsLeast {s : ℕ | ∃ a b c : ℕ , s = a + b + c ∧ a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ ∃ m n p : ℕ , a = 8 * m ∧ b = 8 * n ∧ c = 8 * p} 96 := by
  constructor
  · -- Show that 96 is in the set.
    refine' ⟨24, 32, 40, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try { norm_num }
    all_goals try { 
      use 3, 4, 5 
      all_goals norm_num 
    }
  · -- Show there is no smaller element in the set.
    intro s h 
    rcases h with ⟨a, b, c, hs1, ha1, hb1, hc1, h1, m, n, p, ha2, hb2, hc2⟩
    have heq : m ^ 2 + n ^ 2 = p ^ 2 := by
      have eq1 : a = 8 * m := by linarith 
      have eq2 : b = 8 * n := by linarith 
      have eq3 : c = 8 * p := by linarith 
      rw [eq1, eq2, eq3] at h1 
      nlinarith
    have hm : m > 0 := by
      omega
    have hn : n > 0 := by
      omega
    have hp : p > 0 := by
      omega
    by_contra h
    push_neg at h 
    have h7 : s < 96 := by 
      omega 
    have hperim : s = 8 * (m + n + p) := by
      omega 
    have h8 : m + n + p < 12 := by
      nlinarith
    have h9 : m ≤ 9 := by 
      omega 
    have h10 : n ≤ 9 := by 
      omega 
    have h11 : p ≤ 9 := by 
      omega 
    interval_cases m <;> interval_cases n <;> interval_cases p 
    <;> omega