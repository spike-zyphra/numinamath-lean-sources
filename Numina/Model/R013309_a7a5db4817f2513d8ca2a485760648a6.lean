import Mathlib

theorem algebra_146450 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : 350 / n = m + 3 ∧ 350 / (n - 15) = m) :
    n = 50 ∧ m = 7 := by
  rcases h with ⟨h1, h2⟩
  have h3 : n ≤ 350 := by 
    by_contra h3
    push_neg at h3
    have h4 : 350 / n = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    have h5 : m + 3 = 0 := by 
      omega
    have h6 : m = 0 := by 
      omega
    contradiction
  have h350 : n ≥ 1 := by
    omega
  have h8 : n - 15 ≤ 350 := by
    by_contra h7
    push_neg at h7
    have h9 : 350 / (n - 15) = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    have h10 : m = 0 := by 
      omega
    contradiction
  interval_cases n <;> norm_num at h1 h2 <;> omega