import Mathlib

theorem algebra_307825 {n : ℕ} (h : n ∈ Finset.Icc 10 99) (h' : (n / 10) + (n % 10) + (n / 10) * (n % 10) = n) :
    n % 10 = 9 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h10, h99⟩
  interval_cases n <;> norm_num at h' ⊢ <;> omega