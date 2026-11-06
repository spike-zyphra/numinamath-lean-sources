import Mathlib

theorem number_theory_234201 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    n = 3 * (Nat.digits 10 n).sum^2 ↔ n = 243 ∨ n = 972 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h1, h2⟩
  constructor
  · -- Forward direction
    intro h
    interval_cases n <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction
    rintro (h | h)
    · -- First case
      rw [h]
      norm_num
    · -- Second case
      rw [h]
      norm_num