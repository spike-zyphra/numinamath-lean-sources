import Mathlib

theorem number_theory_94975 (x y : ℕ) (h₀ : x ∈ Finset.Icc 1 6) (h₁ : y ∈ Finset.Icc 1 6)
    (h₂ : 6 ∣ x * y) :
    x + y ≠ 6 := by 
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨hx1, hx2⟩
  rcases h₁ with ⟨hy1, hy2⟩

  -- Now we can try all possible values for x and y in the range [1,6]
  interval_cases x <;> interval_cases y <;> omega