import Mathlib

theorem algebra_105200 {P : Polynomial ℤ} (a b c : ℤ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (hP : P.eval a = 2 ∧ P.eval b = 2 ∧ P.eval c = 2) : ¬∃ k : ℤ, P.eval k = 3 := by 
  rintro ⟨k, hk⟩
  rcases hP with ⟨ha2, hb2, hc2⟩
  have h1 : (k - a) ∣ (P.eval k - P.eval a) := by 
    apply P.sub_dvd_eval_sub
  have h1' : (k - a) ∣ 1 := by 
    rw [show P.eval k - P.eval a = 1 by linarith [hk, ha2]] at h1
    exact h1
  have h2 : (k - b) ∣ (P.eval k - P.eval b) := by 
    apply P.sub_dvd_eval_sub
  have h2' : (k - b) ∣ 1 := by 
    rw [show P.eval k - P.eval b = 1 by linarith [hk, hb2]] at h2
    exact h2
  have h3 : (k - c) ∣ (P.eval k - P.eval c) := by 
    apply P.sub_dvd_eval_sub
  have h3' : (k - c) ∣ 1 := by 
    rw [show P.eval k - P.eval c = 1 by linarith [hk, hc2]] at h3
    exact h3
  have h4 : (k - a) = 1 ∨ (k - a) = -1 := by 
    have h5 : (k - a) ∣ 1 := h1'
    have h6 : (k - a) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h5
    have h7 : (k - a) ≥ -1 := by
      have h8 : -(k - a) ∣ 1 := by
        exact Int.neg_dvd.2 h5
      have h9 : -(k - a) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h8
      omega 
    interval_cases h : (k - a) <;> tauto
  -- Use the fact that k - b divides 1, so it must be 1 or -1
  have h5 : (k - b) = 1 ∨ (k - b) = -1 := by 
    have h6 : (k - b) ∣ 1 := h2'
    have h7 : (k - b) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h6 
    have h8 : (k - b) ≥ -1 := by
      have h9 : -(k - b) ∣ 1 := by
        exact Int.neg_dvd.2 h6
      have h10 : -(k - b) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h9
      omega
    interval_cases h : (k - b) <;> tauto
  -- Use the fact that k - c divides 1, so it must be 1 or -1
  have h6 : (k - c) = 1 ∨ (k - c) = -1 := by 
    have h7 : (k - c) ∣ 1 := h3'
    have h8 : (k - c) ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) h7
    have h9 : (k - c) ≥ -1 := by
      have h10 : -(k - c) ∣ 1 := by 
        exact Int.neg_dvd.2 h7
      have h11 : -(k - c) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h10
      omega
    interval_cases h : (k - c) <;> tauto
  rcases h4 with h4 | h4
  all_goals
    rcases h5 with h5 | h5
    all_goals
      rcases h6 with h6 | h6
      all_goals 
        omega