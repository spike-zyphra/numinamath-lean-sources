import Mathlib

theorem negated_number_theory_62545 (m n : ℤ)
    (hm : m > 0)
    (hn : n > 0) :
    83 ∣ 25 * m + 3 * n ↔ 83 ∣ 3 * m + 7 * n := by
  constructor
  · -- Assume $83 \mid 25m + 3n$, prove $83 \mid 3m + 7n$
    intro h
    omega
  · -- Assume $83 \mid 3m + 7n$, prove $83 \mid 25m + 3n$
    intro h
    omega