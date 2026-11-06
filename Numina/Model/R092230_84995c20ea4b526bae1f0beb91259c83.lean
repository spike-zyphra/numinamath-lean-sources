import Mathlib

theorem number_theory_287887 :
    IsLeast {n | ∃ k : ℕ, n = ∑ i ∈ Finset.range 5, (2 * i + 2 * k) ∧ 7 ∣ n} 70 := by
  constructor
  · -- Show that (70, k) exists
    use 5
    native_decide 
  · -- Show that 70 is the smallest
    intro n hn
    rcases hn with ⟨k, hk_sum, h7⟩
    have h1 : n = 10 * k + 20 := by 
      simp [Finset.sum_range_succ] at hk_sum 
      omega 
    rw [h1] at h7 
    by_contra h
    push_neg at h
    have h2 : k < 5 := by 
      by_contra h
      push_neg at h 
      have : 10 * k + 20 ≥ 70 := by 
        omega 
      omega 
    interval_cases k <;> norm_num at h7 
    <;> omega