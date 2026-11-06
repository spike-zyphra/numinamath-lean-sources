import Mathlib

theorem algebra_269524 {p : Polynomial ℝ} (hp : p = (X^2 + 1) * (X^2 + X - 1)) :
    (X^2 + 1) ∣ p ∧ (X^3 + X^2 + 1) ∣ p + 1 := by
  constructor
  · -- Show that $x^2 + 1$ divides $p$
    rw [hp]
    use (X^2 + X - 1)
    all_goals ring_nf
    all_goals norm_num
  · -- Show that $x^3 + x^2 + 1$ divides $p + 1$
    rw [hp]
    use X
    ring_nf
    all_goals norm_num
    all_goals ring
    all_goals norm_num
    all_goals ring_nf
    all_goals norm_num