import Mathlib

theorem algebra_200239 {x : ℕ → ℝ} (h : ∀ n, 2 * x n = ∑ i in Finset.range (n + 1), x i) :
    ∀ n, x n = x 0 * 4 ^ (n - 1) / 3 ^ n := by
  have eq1 : x 0 = 0 := by 
    have h0 := h 0 
    norm_num [Finset.sum_range_succ] at h0 
    linarith 
  have h1 : ∀ n, x n = 0 := by 
    intro n 
    induction n with 
    | zero => 
      exact eq1 
    | succ n ih => 
      have h2 := h (n + 1) 
      have h3 := h n 
      simp [Finset.sum_range_succ] at h2 h3 
      have h4 : x (n + 1) = 2 * x n := by linarith 
      rw [ih] at h4 
      have h5 : x (n + 1) = 0 := by linarith 
      exact h5 
  intro n 
  have eq2 : x n = 0 := h1 n 
  rw [eq2] 
  rw [eq1] 
  all_goals simp