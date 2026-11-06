import Mathlib

theorem number_theory_113261 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : n / (10 * (n % 10) + (n / 10)) = n % (10 * (n % 10) + (n / 10))) :
    n = 52 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h10, h99⟩
  interval_cases n <;> norm_num at h₁ <;> try { trivial } <;> try { omega }