import Mathlib

theorem algebra_315662 {a b : ℕ → ℝ} (ha : ∀ i ∈ Finset.range 99, a i ≠ 0)
    (hb : ∀ i ∈ Finset.range 100, b i ≠ 0) (h1 : ∀ k ∈ Finset.range 99, ∑ i in Finset.range (k + 1), a i = ∑ i in Finset.range (k + 1), b i - b k)
    (h2 : ∑ i in Finset.range 90, a i = 50 * 99) :
    ∑ i in Finset.range 100, b i = 100 := by
  have h3 := h1 0 (by simp)
  have h3' : ∑ i in Finset.range (0 + 1), a i = a 0 := by 
    simp [Finset.sum_range_succ]
  have h4' : ∑ i in Finset.range (0 + 1), b i = b 0 := by 
    simp [Finset.sum_range_succ]
  rw [h3', h4'] at h3
  have h5 : a 0 = 0 := by 
    linarith
  have h6 : a 0 ≠ 0 := by 
    apply ha 0 
    simp
  exfalso 
  contradiction