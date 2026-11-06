import Mathlib

open Finset Real

theorem inequalities_276904 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ range n, 0 < x i) :
    ∑ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) ≥ ∑ i ∈ range n, x i := by
  have hx1 {i} (hi : i ∈ range n) : 0 < x ((i + 1) % n) := by
    apply hx
    simp only [mem_range]
    exact Nat.mod_lt (i + 1) hn
  -- we have 0 < x ((i + 1) % n) for all i ∈ range n
  have h1 : ∀ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n) ≥ 2 * (x i) := by
    intro i hi
    have hx2 : 0 < x ((i + 1) % n) := hx1 hi
    have h2 : (x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n) - 2 * (x i) ≥ 0 := by
      have h3 : (x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n) - 2 * (x i) = ((x i) ^ 2 - 2 * (x i) * x ((i + 1) % n) + (x ((i + 1) % n) ^ 2)) / x ((i + 1) % n) := by
        field_simp [hx2]
        ring
      rw [h3]
      have h4 : (x i) ^ 2 - 2 * (x i) * x ((i + 1) % n) + (x ((i + 1) % n) ^ 2) = ((x i) - x ((i + 1) % n)) ^ 2 := by
        ring
      rw [h4]
      have h5 : x ((i + 1) % n) > 0 := hx2
      have h6 : ((x i) - x ((i + 1) % n)) ^ 2 ≥ 0 := sq_nonneg ((x i) - x ((i + 1) % n))
      have h7 : ((x i) - x ((i + 1) % n)) ^ 2 / x ((i + 1) % n) ≥ 0 := by
        apply div_nonneg h6 (by linarith)
      linarith
    linarith
  have h2 : ∑ i ∈ range n, ((x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n)) ≥ ∑ i ∈ range n, 2 * (x i) := by
    apply sum_le_sum
    intro i hi
    have h3 : (x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n) ≥ 2 * (x i) := h1 i hi
    linarith
  have h3 : ∑ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) + ∑ i ∈ range n, x ((i + 1) % n) ≥ 2 * (∑ i ∈ range n, x i) := by 
    have h4 : ∑ i ∈ range n, (2 * (x i)) = 2 * (∑ i ∈ range n, x i) := by 
      simp [sum_mul, mul_sum]
    have h5 : ∑ i ∈ range n, ((x i) ^ 2 / x ((i + 1) % n) + x ((i + 1) % n)) = 
      ∑ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) + ∑ i ∈ range n, x ((i + 1) % n) := by 
        simp [sum_add_distrib]
    linarith [h5, h4, h2]
  -- show that ∑ i ∈ range n, x ((i + 1) % n) = ∑ i ∈ range n, x i
  have hsum : ∑ i ∈ range n, x ((i + 1) % n) = ∑ i ∈ range n, x i := by 
    nth_rw 1 3 [show n = (n - 1) + 1 by omega]
    rw [sum_range_succ, sum_range_succ']
    congrm ?_ + x (?_)
    · apply sum_congr rfl
      simp
      intro i hi
      congr
      apply Nat.mod_eq_of_lt
      omega
    · simp [show n - 1 + 1 = n by omega]
  -- so we have the result 
  linarith [h3, hsum]