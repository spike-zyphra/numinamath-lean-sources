import Mathlib

open Real
open scoped BigOperators

theorem inequalities_303308 (n : ℕ) (hn : 2 ≤ n) :
  ∑ k in Finset.Icc 1 (n - 1), n / (n - k) * (1 / 2 ^ k) < 4 := by 
  have h2 : ∀ k : ℕ, k ∈ Finset.Icc 1 (n - 1) → n / (n - k) * (1 / 2 ^ k) = 0 := by 
    intro k hk
    simp [Finset.mem_Icc] at hk
    rcases hk with ⟨h3, h4⟩
    have h3' : k ≥ 1 := by linarith
    have h5 : 1 / 2 ^ k = 0 := by
      have h6 : 2 ^ k > 1 := by
        have h7 : k ≥ 1 := by linarith
        have h8 : 2 ^ k ≥ 2 ^ 1 := by 
          apply Nat.pow_le_pow_of_le_right
          all_goals linarith
        have h9 : 2 ^ 1 = 2 := by norm_num
        have h10 : 2 ^ k ≥ 2 := by 
          linarith [h9, h8]
        omega 
      have h11 : 2 ^ k > 0 := by positivity 
      have h12 : 1 / 2 ^ k = 0 := by 
        simp [Nat.div_eq_zero_iff]
        all_goals omega 
      linarith 
    simp [h5]
    all_goals omega 
  have h3 : ∑ k in Finset.Icc 1 (n - 1), n / (n - k) * (1 / 2 ^ k) = 0 := by 
    apply Finset.sum_eq_zero 
    intro k hk 
    have h2' : n / (n - k) * (1 / 2 ^ k) = 0 := h2 k hk 
    simpa using h2' 
  rw [h3]
  all_goals norm_num