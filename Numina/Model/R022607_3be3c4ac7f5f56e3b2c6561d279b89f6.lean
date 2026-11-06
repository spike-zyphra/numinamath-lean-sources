import Mathlib

open Real

theorem number_theory_294129 {n : ℕ} (hn : n > 0) :
    √(∑ i ∈ Finset.range (2 * n), 10 ^ i - ∑ i ∈ Finset.range n, 2 * 10 ^ i) =
    ∑ i ∈ Finset.range n, 3 * 10 ^ i := by 
  have h1 : (∑ i in Finset.range (2 * n), (10 : ℝ) ^ i) - (∑ i in Finset.range n, 2 * (10 : ℝ) ^ i) = ((∑ i in Finset.range n, 3 * (10 : ℝ) ^ i) ) ^ 2 := by
    have h2 : ∀ n : ℕ, (∑ i in Finset.range (2 * n), (10 : ℝ) ^ i) = ((10 : ℝ) ^ (2 * n) - 1) / (9 : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
        <;> norm_num
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
        field_simp
        ring_nf
        <;> norm_num
    have h3 : ∀ n : ℕ, (∑ i in Finset.range n, (2 * (10 : ℝ) ^ i)) = (2 * ((10 : ℝ) ^ n - 1) / (9 : ℝ)) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        ring_nf
        <;> norm_num
    have h4 : ∀ n : ℕ, (∑ i in Finset.range n, (3 * (10 : ℝ) ^ i)) = ((10 : ℝ) ^ n - 1) / (3 : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        ring_nf
        <;> norm_num
    rw [h2 n, h3 n, h4 n]
    field_simp
    ring_nf
    <;> norm_num
  rw [h1]
  have h5 : 0 ≤ ( (∑ i in Finset.range n, 3 * (10 : ℝ) ^ i ) ) := by
    positivity
  rw [Real.sqrt_sq (by positivity)]
  all_goals positivity