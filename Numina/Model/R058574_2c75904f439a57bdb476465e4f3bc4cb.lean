import Mathlib

theorem number_theory_79963 (n : ℕ) :
    n > 0 ∧ n < 1000 ∧ (Nat.digits 10 n).sum^3 = n^2 ↔ n = 1 ∨ n = 27 := by 
  constructor
  · -- Forward direction: if n satisfies the conditions, then n is 1 or 27
    intro h
    rcases h with ⟨h1, h2, h3⟩
    interval_cases n <;> norm_num at h1 h2 h3 ⊢
    <;> tauto
  · -- Backward direction: if n is 1 or 27, then it satisfies the conditions
    rintro (rfl | rfl)
    · -- Check n = 1
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check n = 27
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num