import Mathlib

set_option maxRecDepth 100000000

/-If \[1 \cdot 1987 + 2 \cdot 1986 + 3 \cdot 1985 + \dots + 1986 \cdot 2 + 1987 \cdot 1 = 1987 \cdot 994 \cdot x,\]compute the integer $x.$-/
theorem algebra_13001 (x : ℤ) : ∑ i ∈ Finset.range 1987, (i + 1) * (1987 - (i : ℝ)) = 1987 * 994 * x ↔ x = 663 := by
  -- We can represent the sum as \[\sum_{n = 1}^{1987} n(1988 - n).\]
  -- This is equal to \sum_{n = 1}^{1987} (1988n - n^2) &= 1988 \sum_{n = 1}^{1987} n - \sum_{n = 1}^{1987} n^2
  have : ∑ i ∈ Finset.range 1987, (i + 1) * (1987 - (i : ℝ)) =
      1988 * ∑ i ∈ Finset.range 1987, (i + 1) - ((∑ i ∈ Finset.range 1987, (i + 1)^2) : ℝ) := by
    have : (fun (i : ℕ) ↦ (i + 1) * (1987 - (i : ℝ))) = (fun (i : ℕ) ↦ (1988 * (i + 1)) - (i + 1 : ℝ)^2) := by
      ext i
      ring_nf
    rw [Finset.sum, this, ←Finset.sum, Finset.sum_sub_distrib, (Finset.mul_sum _ _ _).symm]
    simp
  rw [this]
  -- = 1988 \cdot \frac{1987 \cdot 1988}{2} - \frac{1987 \cdot 1988 \cdot 3975}{6}
  have :  ∑ i ∈ Finset.range 1987, (i + 1) = 1987 * 1988 / 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_range_id]
    simp
  rw [this]
  have : ∑ i ∈ Finset.range 1987, (i + 1 : ℝ) ^ 2 = 1987 * 1988 * 3975 / 6 := by
    have : (fun (i : ℕ) ↦ (i + 1 : ℝ) ^ 2) = (fun (i : ℕ) ↦ (i^2 + 2 * i + 1 : ℝ)) := by
      ext i
      ring_nf
    rw [Finset.sum, this, ←Finset.sum, Finset.sum_add_distrib, Finset.sum_add_distrib, (Finset.mul_sum _ _ _).symm]
    simp
    have : ∑ i ∈ Finset.range 1987, (i : ℝ) = ∑ i ∈ Finset.range 1987, i := by simp
    rw [this, Finset.sum_range_id]
    have (n : ℕ) : ∑ i ∈ Finset.range n, (i ^ 2 : ℝ) = (n - 1) * n * (2 * n - 1) / 6 := by
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp
        ring_nf
    rw [this]
    ring_nf
  rw [this]
  ring_nf
  constructor
  . intro hx
    norm_cast at hx
    linarith
  . intro hx
    rw [hx]
    norm_num
