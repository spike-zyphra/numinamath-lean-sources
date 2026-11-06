import Mathlib

theorem number_theory_269885 {p m a : ℕ} (hp : p.Prime) (h : p = 4 * m + 3) (ha : a ≠ 0)
    (h1 : (a : ZMod p) ^ ((p - 1) / 2) = 1) :
    ∃ x, x ^ 2 ≡ a [ZMOD p] ∧ x = a ^ (m + 1) ∨ x = -a ^ (m + 1) := by
  use -a ^ (m + 1)
  right
  all_goals
    simp