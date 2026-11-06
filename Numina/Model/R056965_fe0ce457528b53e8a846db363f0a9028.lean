import Mathlib

theorem algebra_7057 {n : ℕ} (h : n ∈ Finset.Icc 10 99) (h1 : n = (n / 10)^3 + (n % 10)^2) :
    n = 24 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h10, h99⟩
  interval_cases n <;> norm_num at h1 <;> omega