import Mathlib

theorem number_theory_280754 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    (n * 1000 + n) / n = 1001 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  have h3 : n * 1000 + n = n * 1001 := by
    ring
  have h4 : n ≠ 0 := by
    linarith
  calc 
    (n * 1000 + n) / n = (n * 1001) / n := by
      rw [h3]
    _ = 1001 := by
      field_simp [h4]
      all_goals omega