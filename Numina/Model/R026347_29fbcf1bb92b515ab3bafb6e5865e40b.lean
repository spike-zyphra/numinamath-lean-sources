import Mathlib

def S : ℕ := ∑ k in (Finset.Ico 1 100).filter (fun x => Nat.Coprime x 100), k

theorem number_theory_4290 (n : ℕ) (h₀ : 0 < n) (h₁ : 10 ^ n ≤ S ∧ S < 10 ^ (n + 1)) :
    S / 10 ^ (n - 2) = 200 := by
  have h2 : S = 2000 := by
    native_decide
  have h3 : n ≤ 3 := by
    have h4 : 10 ^ n ≤ 2000 := by 
      rw [h2] at h₁
      exact h₁.left
    by_contra h
    push_neg at h
    have h5 : n ≥ 4 := by 
      omega
    have h6 : 10 ^ n ≥ 10 ^ 4 := by 
      have h7 : n ≥ 4 := h5
      have h8 : 10 ^ n ≥ 10 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h7
      exact h8
    norm_num at h6
    linarith
  have h8 : n > 2 := by 
    have h9 : 2000 < 10 ^ (n + 1) := by 
      rw [h2] at h₁
      exact h₁.right
    by_contra h
    push_neg at h
    have h5 : n ≤ 2 := by omega
    have h6 : n + 1 ≤ 3 := by omega
    have h10_pow : 10 ^ (n + 1) ≤ 10 ^ 3 := by
      have h11 : n + 1 ≤ 3 := by
        omega
      have h12 : 10 ^ (n + 1) ≤ 10 ^ 3 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h11
      exact h12
    norm_num at h10_pow
    linarith
  have hn3 : n = 3 := by
    omega
  simp [h2, hn3]
  all_goals norm_num