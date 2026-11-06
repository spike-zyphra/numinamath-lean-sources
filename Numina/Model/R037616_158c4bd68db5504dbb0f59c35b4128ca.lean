import Mathlib

theorem algebra_287054 {a : ℕ → ℝ} (ha : ∀ n, 3 * a (n + 1) + a n = 4) (ha1 : a 0 = 9) :
    IsLeast {n | |∑ k in Finset.range n, a k - n - 6| < 125⁻¹} 7 := by
  have h1 : ∀ n, a n = 8 * (-1/3)^(n : ℕ) + 1 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num [ha1]
    | succ n ih =>
      have h2 := ha n
      simp [pow_succ, pow_zero, mul_add, mul_assoc] at h2 ⊢
      linarith [ih, h2]
  have h3 : ∀ n : ℕ, ∑ k in Finset.range n, a k = 6 * (1 - (-1/3 : ℝ)^n) + n := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h1]
      <;> field_simp 
      <;> ring_nf 
  have h4 : 7 ∈ {n | |∑ k in Finset.range n, a k - n - 6| < 125⁻¹} := by 
    rw [Set.mem_setOf_eq]
    rw [h3 7]
    norm_num [abs_lt]
  have h5 : ∀ n, n ∈ {n | |∑ k in Finset.range n, a k - n - 6| < 125⁻¹} → 7 ≤ n := by
    intro n hn
    have h6 : |∑ k in Finset.range n, a k - n - 6| < 125⁻¹ := by 
      simpa using hn
    by_contra h 
    push_neg at h 
    have h7 : n < 7 := by linarith
    have h8 : ∑ k in  Finset.range n, a k = 6 * (1 - (-1/3 : ℝ) ^ n) + n := by
      apply h3
    rw [h8] at h6 
    interval_cases n <;> norm_num [abs_lt] at h6 ⊢
  exact ⟨h4, h5⟩