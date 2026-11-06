import Mathlib

theorem number_theory_196589 (a : Fin 4 → ℕ) (ha : a 0 ≠ a 2 ∨ a 1 ≠ a 3) :
    ∃ q, q > 0 ∧ (a 0 * 1000 + a 1 * 100 + a 2 * 10 + a 3) % q = 0 ∧
    (a 3 * 1000 + a 0 * 100 + a 1 * 10 + a 2) % q = 0 ∧
    (a 2 * 1000 + a 3 * 100 + a 0 * 10 + a 1) % q = 0 ∧
    (a 1 * 1000 + a 2 * 100 + a 3 * 10 + a 0) % q = 0 := by
  use 1
  constructor
  · norm_num
  constructor
  · -- Show $(a_0 \cdot 1000 + a_1 \cdot 100 + a_2 \cdot 10 + a_3) % 1 = 0$
    omega
  constructor
  · -- Show $(a_3 \cdot 1000 + a_0 \cdot 100 + a_1 \cdot 10 + a_2) % 1 = 0$
    omega
  constructor
  · -- Show $(a_2 \cdot 1000 + a_3 \cdot 100 + a_0 \cdot 10 + a_1) % 1 = 0$
    omega
  · -- Show $(a_1 \cdot 1000 + a_2 \cdot 100 + a_3 \cdot 10 + a_0) % 1 = 0$
    omega