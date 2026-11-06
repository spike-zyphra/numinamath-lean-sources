import Mathlib

theorem algebra_278698 (p : ℕ) (x : ℝ) (hx : x ≠ 1) :
    ∑ i ∈ Finset.Icc 1 p, i * x ^ i =
    (x - (p + 1) * x ^ (p + 1) + p * x ^ (p + 2)) / (1 - x) ^ 2 := by
  induction p with
  | zero =>
    simp
    <;> field_simp [(show (1 - x : ℝ) ≠ 0 by intro h; apply hx; linarith)]
    <;> ring
  | succ p ih =>
    rw [Finset.sum_Icc_succ_top (by linarith)]
    rw [ih]
    field_simp [(show (1 - x : ℝ) ≠ 0 by intro h; apply hx; linarith)] at *
    ring_nf
    <;> field_simp [(show (1 - x : ℝ) ≠ 0 by intro h; apply hx; linarith)]
    <;> ring