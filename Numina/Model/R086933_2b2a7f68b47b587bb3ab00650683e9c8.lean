import Mathlib

theorem algebra_177752 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (n / 10) + (n % 10) = 12)
    (h₂ : 10 * (n % 10) + (n / 10) = n - 36) :
    n = 84 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> try { omega } <;> try { trivial }
  <;> try { omega }
  <;> try { trivial }