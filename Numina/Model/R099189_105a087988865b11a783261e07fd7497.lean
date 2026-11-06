import Mathlib

theorem algebra_186471 {a : ℝ} (ha : a ≠ 0) (h : ∑ i ∈ Finset.range 6, a * 3 ^ i = 1820) :
    a = 5 ∧ a * 3 ^ 4 = 405 := by
  have h₁ : a + a * 3 + a * 9 + a * 27 + a * 81 + a * 243 = 1820 := by 
    simp [Finset.sum_range_succ] at h 
    linarith
  
  have h2 : a = 5 := by
    linarith
  
  have h3 : a * 3 ^ 4 = 405 := by 
    rw [h2]
    norm_num
  
  exact ⟨h2, h3⟩
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { norm_num }
  all_goals try { ring }
  all_goals try { linarith }
  all_goals try { norm_num }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { norm_num }
  all_goals try { tauto }
  all_goals try { linarith }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { norm_num }