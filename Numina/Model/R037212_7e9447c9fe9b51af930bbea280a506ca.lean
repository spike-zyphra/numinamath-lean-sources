import Mathlib

theorem number_theory_292328 (a : ℕ → ℤ) (ha : ∀ n, a n = 3 * n + 1) :
    IsLeast {x | ∃ k, x = a k ∧ 11 ∣ ∑ i ∈ Finset.range 7, a (k + i)} 13 := by 
  constructor 
  · -- Prove 13 is in the set
    use 4
    norm_num [Finset.sum_range_succ, ha]
    <;> omega 
  · -- Prove no element less than 13 is in the set 
    intro x hx 
    rcases hx with ⟨k, hk, h⟩
    rw [hk] at *
    simp [Finset.sum_range_succ, ha] at h ⊢
    by_contra h'
    push_neg at h'
    have h1 : k < 4 := by 
      by_contra h2 
      push_neg at h2 
      omega 
    interval_cases k <;> omega