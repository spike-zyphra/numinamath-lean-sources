import Mathlib

theorem algebra_301875 {a q : ℝ} (hq : q ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, a * q ^ i = a * (1 - q ^ n) / (1 - q) := by
  induction n with
  | zero =>
    simp
    <;> ring_nf <;> simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    field_simp [(show 1 - q ≠ 0 by intro h; apply hq; linarith)]
    <;> ring_nf
    <;> simp
    all_goals ring
  all_goals try simp_all