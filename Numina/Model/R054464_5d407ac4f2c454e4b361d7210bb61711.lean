import Mathlib

theorem number_theory_264043 (M : Set ℕ) (hM : M = {x | 1 ≤ x ∧ x ≤ 2007})
    (hM' : ∀ n ∈ M, ∀ k, n + (k * (n + 1)) ∈ M) :
    ∃ m, ∀ n, n > m → n ∈ M := by
  have h1 : 1 ∈ M := by 
    rw [hM]
    exact ⟨by norm_num, by norm_num⟩
  have h2 := hM' 1 h1 1004
  norm_num [hM] at h2 
  all_goals omega