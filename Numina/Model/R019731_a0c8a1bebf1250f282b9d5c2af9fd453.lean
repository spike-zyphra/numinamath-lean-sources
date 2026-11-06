import Mathlib

theorem algebra_21866 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 10) (h₁ : ∃ k, k^2 = ∑ i in Finset.Icc 1 10 \ {n}, i) :
    n = 6 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₁ with ⟨k, hk⟩
  rcases h₀ with ⟨h₃, h₄⟩
  have h3 : ∑ i in Finset.Icc 1 10 \ {n}, i = 55 - n := by
    interval_cases n <;> try { 
      native_decide
    }
  rw [h3] at hk
  interval_cases n <;> try { 
    norm_num at hk
    all_goals
    have h4 : k ≤ 7 := by nlinarith
    interval_cases k <;> omega
  }