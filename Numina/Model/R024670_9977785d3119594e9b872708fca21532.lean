import Mathlib

theorem algebra_9201 {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ n → 4 * (∑ i in Finset.range n, a i) = 3 * a n + 2 ^ (n + 1)) :
    StrictMono a ↔ a 0 = 2 / 5 := by
  have h0 := ha 0 (by norm_num)
  norm_num [Finset.sum_range_zero] at h0
  have h1 := ha 1 (by norm_num)
  have h1' : 4 * a 0 = 3 * a 1 + 4 := by 
    simp [Finset.sum_range_succ] at h1 ⊢
    linarith
  have h2 : a 0 = -2 / 3 := by linarith
  have ha1 : a 1 = -20 / 9 := by
    have eq1 : 4 * a 0 = 3 * a 1 + 4 := h1'
    rw [h2] at eq1
    linarith
  constructor
  · -- Assume `a` is strictly increasing
    intro h
    exfalso
    have h3 : a 1 > a 0 := by 
      apply h
      all_goals norm_num
    have h4 : a 1 ≤ a 0 := by 
      have h5 : a 1 = -20 / 9 := ha1
      have h6 : a 0 = -2 / 3 := h2
      linarith
    linarith
  · -- Assume `a 0 = 2 / 5`
    intro h
    exfalso
    linarith