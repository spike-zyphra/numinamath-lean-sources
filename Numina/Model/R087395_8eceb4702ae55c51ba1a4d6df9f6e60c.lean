import Mathlib

theorem algebra_238859 (n : ℕ) (h : n > 0) :
    √(∑ i ∈ Finset.range n, (2018^2 : ℝ)) = 2018^10 ↔ n = 2018^18 := by
  constructor
  · -- Assume $\sqrt{\sum_{i \in \text{range } n} 2018^2} = 2018^{10}$, prove $n = 2018^{18}$.
    intro h_eq
    have h_sum : ∑ i in Finset.range n, (2018^2 : ℝ) = (n : ℝ) * (2018 : ℝ)^2 := by
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> ring
    rw [h_sum] at h_eq
    have h_sq : (Real.sqrt ((n : ℝ) * (2018 : ℝ)^2)) ^ 2 = ((2018 ^ 10 : ℝ)) ^ 2 := by
      rw [h_eq]
    have h_left : (Real.sqrt ((n : ℝ) * (2018 : ℝ) ^ 2)) ^ 2 = (n : ℝ) * (2018 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h_right : ((2018 ^ 10 : ℝ)) ^ 2 = (2018 : ℝ) ^ (20 : ℕ) := by
      norm_num
    rw [h_left, h_right] at h_sq
    have h_eq_nat : (n : ℝ) * (2018 : ℝ) ^ 2 = (2018 : ℝ) ^ (20 : ℕ) := by
      linarith
    have h_eq_nat' : n = 2018 ^ 18 := by
      have h1 : (n : ℝ) * (2018 : ℝ) ^ 2 = (2018 : ℝ) ^ (20 : ℕ) := by
        linarith
      have h2 : (n : ℝ) * (2018 : ℝ) ^ 2 = (2018 ^ 20 : ℝ) := by
        norm_num at h1 ⊢
        linarith
      have h2_nat : n * (2018 ^ 2) = (2018 ^ 20) := by
        exact_mod_cast h2
      nlinarith
    exact h_eq_nat'
  · -- Assume $n = 2018^{18}$, prove $\sqrt{\sum_{i \in \text{range } n} 2018^2} = 2018^{10}$.
    intro h_eq
    rw [show n = 2018 ^ 18 by linarith]
    have h_sum : ∑ i in Finset.range (2018 ^ 18), (2018^2 : ℝ) = (2018 ^ 18 : ℝ) * (2018 : ℝ)^2 := by
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> ring
    rw [h_sum]
    -- sqrt of ((2018 ^ 18) * (2018 ^ 2))
    -- becomes sqrt((2018 ^ (18 + 2))).
    -- which is sqrt((2018)^20) = (2018)^10.
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num