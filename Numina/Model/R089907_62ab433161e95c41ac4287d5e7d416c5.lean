import Mathlib

theorem number_theory_155262 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    n^2 = (Nat.digits 10 n).sum^3 ↔ n = 27 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h10, h99⟩
  constructor
  · -- Assume n^2 = (Nat.digits 10 n).sum^3, prove n = 27
    intro h_eq
    interval_cases n <;> norm_num at h_eq <;> norm_num at *
    <;> try { trivial }
    <;> try { contradiction }
  · -- Assume n = 27, prove n^2 = (Nat.digits 10 n).sum^3
    intro h_eq
    rw [h_eq]
    norm_num