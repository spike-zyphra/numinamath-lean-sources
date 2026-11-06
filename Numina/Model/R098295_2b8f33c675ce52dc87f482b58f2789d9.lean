import Mathlib

theorem number_theory_194983 (n : ℕ) (h : n ∈ Finset.Icc 100 999) :
    n = 19 * (Nat.digits 10 n).sum ↔ n = 114 ∨ n = 133 ∨ n = 152 ∨ n = 171 ∨ n = 190 ∨
    n = 209 ∨ n = 228 ∨ n = 247 ∨ n = 266 ∨ n = 285 ∨ n = 399 := by 
  rw [Finset.mem_Icc] at h 
  rcases h with ⟨h1, h2⟩ 
  constructor 
  · -- Assume n = 19 * (Nat.digits 10 n).sum, prove n ∈ the set.
    intro h_eq
    interval_cases n <;> norm_num at h_eq <;> norm_num at *
    <;> omega 
  · -- Assume n ∈ the set, prove n = 19 * (Nat.digits 10 n).sum
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals 
      norm_num