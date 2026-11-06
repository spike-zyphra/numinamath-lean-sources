import Mathlib

theorem algebra_16588 : (Nat.Prime 5)∧(¬Nat.Prime 6)∧(Nat.Prime 7)∧(Nat.Prime 97)∧(¬∃n<10, n > 7 ∧ Nat.Prime n)∧(¬∃n<100, n > 97 ∧ Nat.Prime n)∧(5 * 7 * 97 = 3395) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- Show that there is no one-digit prime larger than 7
    intro h
    rcases h with ⟨n, hn1, hn2, hn3⟩
    interval_cases n <;> norm_num at hn3 ⊢ <;> try { tauto }
  constructor
  · -- Show that there is no two-digit prime larger than 97
    intro h
    rcases h with ⟨n, hn1, hn2, hn3⟩
    interval_cases n <;> norm_num at hn3 ⊢ <;> try { tauto }
  · -- Compute the multiplication
    norm_num