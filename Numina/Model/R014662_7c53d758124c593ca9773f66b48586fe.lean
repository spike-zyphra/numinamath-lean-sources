import Mathlib

theorem number_theory_167257 (a : ℕ → ℤ) (ha : ∀ n, a n = a 0 + 3 * n) (h : ∑ i ∈ Finset.range 6, a (n + i) = 159) :
    a n = 19 := by 
  have eq2 : ∑ i in Finset.range 6, a (n + i) = a n + a (n + 1) + a (n + 2) + a (n + 3) + a (n + 4) + a (n + 5) := by 
    simp [Finset.sum_range_succ, add_assoc]
    <;> ring
  rw [eq2] at h 
  simp [ha (n + 0), ha (n + 1), ha (n + 2), ha (n + 3), ha (n + 4), ha (n + 5)] at h
  have eq3 : a n = 19 := by 
    have h1 : a 0 + 3 * (n : ℤ) = a n := by 
      have h2 : a n = a 0 + 3 * n := ha n
      linarith [h2]
    -- Solving from linear equation on h
    linarith [h, ha n]
  linarith [eq3]