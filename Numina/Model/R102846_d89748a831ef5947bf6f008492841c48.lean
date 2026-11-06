import Mathlib

theorem algebra_202480 (n : ℕ) :
    (n = 20 → (2 * n, n / 2) = (40, 10)) ∧
    (n = 48 → (2 * n, n / 2) = (96, 24)) ∧
    (n = 34 → (2 * n, n / 2) = (68, 17)) := by
  constructor
  · -- Proof for n = 20
    intro h
    rw [h]
    all_goals norm_num
  constructor
  · -- Proof for n = 48
    intro h
    rw [h]
    all_goals norm_num
  · -- Proof for n = 34
    intro h
    rw [h]
    all_goals norm_num