import Mathlib

theorem algebra_213970 (x : ℤ) (h : ∑ i ∈ Finset.range 2011, (x + i) = 2011) :
    x + 2010 = 1006 := by 
  have h1 : ∑ i in Finset.range 2011, (x + i) = 2011 * x + ∑ i in Finset.range 2011, (i : ℤ) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_range]
    <;> ring_nf <;> omega
  rw [h1] at h 
  have h2 : ∑ i in Finset.range 2011, (i : ℤ) = (2010 * 2011) / 2 := by 
    native_decide 
  rw [h2] at h 
  omega