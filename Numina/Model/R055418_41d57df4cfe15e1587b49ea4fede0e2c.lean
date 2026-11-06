import Mathlib

theorem algebra_327689 (a d : ℝ) (h₀ : a + d ≠ 0) (h₁ : ∑ i ∈ Finset.range 100, (a + d * i) = 100)
    (h₂ : ∑ i ∈ Finset.range 100, (a + d * (999 - i)) = 1000) :
    a = 0.505 := by
  have h_sum₁ : ∑ i in Finset.range 100, (a + d * i) = 100 * a + 4950 * d := by
    simp [Finset.sum_range_succ]
    ring_nf
  have h_sum₂ : ∑ i in Finset.range 100, (a + d * (999 - i)) = 100 * a + 94950 * d := by
    simp [Finset.sum_range_succ]
    ring_nf
  rw [h_sum₁] at h₁
  rw [h_sum₂] at h₂
  have eq1 : 100 * a + 4950 * d = 100 := by
    linarith
  have eq2 : 100 * a + 94950 * d = 1000 := by
    linarith
  have h_d : d = 1 / 100 := by
    linarith
  have h_a : a = 0.505 := by
    rw [h_d] at eq1
    norm_num at eq1
    have : a = 50.5 / 100 := by linarith
    rw [this]
    norm_num
  exact h_a