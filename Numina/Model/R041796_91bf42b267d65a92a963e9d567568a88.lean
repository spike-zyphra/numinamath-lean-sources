import Mathlib

theorem number_theory_290233 {n m : ℕ} (h₀ : n > 0) (h₁ : m > 0)
    (h₂ : n / m = 12) (h₃ : n % m = 3) :
    IsLeast {x | ∃ n m, x = n ∧ n > 0 ∧ m > 0 ∧ n / m = 12 ∧ n % m = 3} 51 := by 
  constructor
  · -- Show 51 is in the set 
    use 51, 4
    all_goals norm_num
  · -- Show 51 is the smallest element in the set 
    intro x h
    rcases h with ⟨n, m, hx, hn, hm, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : n < 51 := by 
      omega
    have h5 : n / m = 12 := h2
    have h6 : n % m = 3 := h3
    have h7 : n = 12 * m + 3 := by 
      rw [←Nat.div_add_mod n m]
      rw [h5, h6]
      all_goals omega
    have h8 : m < 4 := by
      omega
    have h9 : m > 3 := by
      by_contra h
      push_neg at h
      have h10 : m ≤ 3 := by omega
      have h11 : n % m < m := by
        apply Nat.mod_lt
        all_goals omega
      omega
    all_goals omega