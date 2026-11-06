import Mathlib

theorem algebra_214780 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = (a n + 1) ^ 2 / 4) :
    ∑ i in Finset.range 20, a i = 0 := by
  have ha0 := hsum 0
  simp at ha0
  have ha0_eq : a 0 = -1 := by 
    nlinarith
  
  rcases ha with ⟨r, hr⟩

  have ha1 : a 1 = a 0 * r ^ 1 := hr 1

  simp [ha0_eq] at ha1

  have ha1_eq := hsum 1

  simp [Finset.sum_range_succ, ha0_eq, ha1] at ha1_eq

  nlinarith [sq_nonneg (a 1 + 1)]