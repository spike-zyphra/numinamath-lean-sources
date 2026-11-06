import Mathlib

theorem algebra_100247 (a d : ℤ) (h₀ : d ≠ 0) (h₁ : (a + 4 * d) ^ 2 + (a + 6 * d) ^ 2 + 16 * d = (a + 8 * d) ^ 2 + (a + 10 * d) ^ 2) :
    ∑ i ∈ Finset.range 15, (a + i * d) = 15 := by
  have h2 : a + 7 * d = 1 := by
    have h3 : (a + 4 * d) ^ 2 + (a + 6 * d) ^ 2 + 16 * d = (a + 8 * d) ^ 2 + (a + 10 * d) ^ 2 := h₁
    ring_nf at h3
    have h4 : -16 * a * d - 112 * d^2 + 16 * d = 0 := by
      linarith
    have h5 : 16 * d * (a + 7 * d - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case 1: 16 * d = 0, so d = 0, but h₀ says d ≠ 0, contradiction
      have h8 : d = 0 := by 
        linarith
      contradiction
    · -- Case 2: a + 7 * d - 1 = 0, which means a + 7 * d = 1, which is our goal
      linarith
  have h3 : ∑ i in Finset.range 15, (a + i * d) = 15 * (a + 7 * d) := by
    simp [Finset.sum_range_succ]
    ring_nf
    <;> simp [add_mul, mul_add]
    <;> ring
  rw [h3]
  rw [h2]
  all_goals linarith