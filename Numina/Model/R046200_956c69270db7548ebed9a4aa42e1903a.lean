import Mathlib

theorem number_theory_65996 {p : Polynomial ℤ} {a b : ℤ} (h : p.eval a - p.eval b = 1) :
    |a - b| = 1 := by 
  have h1 : (a - b) ∣ (p.eval a - p.eval b) := by
    apply p.sub_dvd_eval_sub
  rw [h] at h1
  have h2 : (a - b) = 1 ∨ (a - b) = -1 := by
    have h3 : (a - b) ∣ 1 := h1
    have h4 : (a - b) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (a - b) ≥ -1 := by
      have h6 : (- (a - b)) ∣ 1 := by
        exact Int.neg_dvd.2 h3
      have h7 : (- (a - b)) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases (a - b) <;> try { tauto }
    all_goals try { omega }
  cases h2 with
  | inl h3 =>
    rw [h3]
    all_goals norm_num
  | inr h3 =>
    rw [h3]
    all_goals norm_num