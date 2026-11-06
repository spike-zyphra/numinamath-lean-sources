import Mathlib

theorem number_theory_305876 {M : ℕ} (hM : ∃ k, M = k^2) (hM1 : M ∈ Finset.Icc 1000 9999)
    (hM2 : ∃ l, M - 3000 + 3 = l^2) (hM3 : M - 3000 + 3 ∈ Finset.Icc 1000 9999) :
    M = 4761 := by
  rcases hM with ⟨k, rfl⟩
  rcases hM2 with ⟨l, h⟩
  rw [Finset.mem_Icc] at hM1 hM3
  norm_num at hM1 hM3
  have h1 : k ≤ 99 := by
    nlinarith
  have h2 : k ≥ 32 := by
    nlinarith
  have h3 : l ≤ 99 := by
    nlinarith
  have h4 : l ≥ 32 := by
    nlinarith
  interval_cases k <;> try {
    all_goals
      { 
        interval_cases l <;> omega 
      }
  }