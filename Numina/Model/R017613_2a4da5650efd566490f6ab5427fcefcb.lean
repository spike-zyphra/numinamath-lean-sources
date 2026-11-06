import Mathlib

open Finset Real

theorem inequalities_114688 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) :
    ∑ i ∈ range n, (a i)^2 ≥ (∑ i ∈ range n, a i)^2 / n := by
  have h1 : n ≥ 1 := by linarith
  have h2 : (∑ i in range n, a i) ^ 2 ≤ n * ∑ i in range n, (a i) ^ 2 := by
    have h3 : (∑ i in range n, a i) ^ 2 ≤ n * ∑ i in range n, (a i) ^ 2 := by
      have h4 : (∑ i in range n, a i) ^ 2 = (∑ i in range n, (a i * (1 : ℝ))) ^ 2 := by
        congr
        <;> funext i
        <;> simp
      rw [h4]
      have h6 : (∑ i in range n, (a i * (1 : ℝ))) ^ 2 ≤ (∑ i in range n, (a i) ^ 2) * (∑ i in range n, ((1 : ℝ) )^2) := by
        apply Finset.sum_mul_sq_le_sq_mul_sq
      have h7 : (∑ i in range n, ((1 : ℝ) )^2 ) = (n : ℝ) := by
        simp [Finset.sum_const, Finset.card_range, pow_two]
        <;> ring_nf <;> norm_num
      have h7' : (∑ i in range n, (a i) ^ 2) * (∑ i in range n, ((1 : ℝ) )^2 ) = (∑ i in range n, (a i) ^ 2) * (n : ℝ) := by
        rw [h7]
      nlinarith
    linarith
  have hn' : (n : ℝ) > 0 := by exact_mod_cast (show (0 : ℕ) < n from hn)
  have h3 : ∑ i in range n, (a i) ^ 2 ≥ (∑ i in range n, a i) ^ 2 / (n : ℝ) := by
    have h4 : (n : ℝ) > 0 := hn'
    have h5 : (∑ i in range n, a i) ^ 2 ≤ (n : ℝ) * ∑ i in range n, (a i) ^ 2 := by linarith [h2]
    have h6 : (∑ i in range n, a i) ^ 2 / (n : ℝ) ≤ ∑ i in range n, (a i) ^ 2 := by
      have h7 : (n : ℝ) > 0 := h4
      apply (div_le_iff₀ h7).mpr
      nlinarith
    linarith
  exact h3