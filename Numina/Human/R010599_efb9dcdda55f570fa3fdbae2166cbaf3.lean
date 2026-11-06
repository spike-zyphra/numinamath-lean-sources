import Mathlib

theorem algebra_93613 {a d : ℤ} (h₀ : ∑ i ∈ Finset.range 10, (a + d * i) = 100) (h₁ : ∑ i ∈ Finset.range 100, (a + d * i) = 10) :
    ∑ i ∈ Finset.range 110, (a + d * i) = -110 := by 
  have h2 : ∑ i in Finset.range 10, (a + d * i) = 10 * a + 45 * d := by
    simp only [Finset.sum_range_succ, add_mul, mul_add]
    ring
  have h3 : ∑ i in Finset.range 100, (a + d * i) = 100 * a + 4950 * d := by 
    simp only [Finset.sum_range_succ, add_mul, mul_add]
    ring
  have h4 : ∑ i in Finset.range 110, (a + d * i) = 110 * a + 5995 * d := by 
    simp only [Finset.sum_range_succ, add_mul, mul_add]
    ring
  rw [h2] at h₀
  rw [h3] at h₁
  rw [h4]
  omega