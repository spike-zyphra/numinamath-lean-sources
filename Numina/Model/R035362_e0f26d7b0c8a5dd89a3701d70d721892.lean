import Mathlib

theorem algebra_97810 {B J N : ℕ} (hB : B > 0) (hJ : J > 0) (hN : N > 1)
(hcost : N*(B * 4 + J * 5) = 253) :
N * J * 5 = 165 := by
  have h1 : N ∣ 253 := by
    use B * 4 + J * 5
    all_goals linarith
  have h2 : N = 11 ∨ N = 23 ∨ N = 253 := by
    have h3 : N ∣ 253 := h1
    have h4 : N ≤ 253 := by
      exact Nat.le_of_dvd (by norm_num) h3
    interval_cases N <;> norm_num at h3 ⊢
    <;> try { tauto }
  rcases h2 with h2 | h2 | h2
  · -- Case N = 11
    have h3 : B * 4 + J * 5 = 23 := by 
      rw [h2] at hcost 
      nlinarith 
    have h4 : B = 2 := by
      omega
    have h5 : J = 3 := by
      omega 
    calc
      N * J * 5 = 11 * 3 * 5 := by 
        rw [h2, h5]
      _ = 165 := by
        norm_num 
  · -- Case N = 23
    have h3 : B * 4 + J * 5 = 11 := by 
      rw [h2] at hcost 
      nlinarith 
    have h4 : B ≤ 2 := by
      omega
    have h5 : J ≤ 2 := by
      omega 
    interval_cases B <;> interval_cases J <;> omega 
  · -- Case N = 253
    have h3 : B * 4 + J * 5 = 1 := by 
      rw [h2] at hcost 
      nlinarith 
    omega