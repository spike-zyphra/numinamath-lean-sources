import Mathlib

theorem algebra_12717 (a : ℕ → ℝ) (h : ∃ d, ∀ n, a n = a 0 + d * n)
    (h1 : ∑ i in Finset.range 4, a i ≤ 4) (h2 : ∑ i in Finset.range 5, a i ≥ 15) :
    a 4 ≥ 7 := by
  rcases h with ⟨d, hd⟩

  have h4 : a 4 = a 0 + 4 * d := by 
    specialize hd 4
    rw [hd]
    ring

  have s4 : ∑ i in Finset.range 4, a i = 4 * a 0 + 6 * d := by 
      simp [Finset.sum_range_succ, hd 1, hd 2, hd 3]
      ring

  have s5 : ∑ i in Finset.range 5, a i = 5 * a 0 + 10 * d := by 
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4]
    ring
  
  rw [s4] at h1 
  rw [s5] at h2 

  linarith [h1, h2, h4]