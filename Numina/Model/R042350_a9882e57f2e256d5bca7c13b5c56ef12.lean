import Mathlib

theorem algebra_229198 {n : ℕ} (x : ℝ) (h : ∑ i ∈ Finset.range (n + 1), x ^ i = (1 - x ^ (n + 1)) / (1 - x)) :
    ∑ i ∈ Finset.range n, (i + 1) * x ^ i = (1 - (n + 1) * x ^ n + n * x ^ (n + 1)) / (1 - x) ^ 2 := by 
  have eq1 : (1 - x) ≠ 0 := by
    by_contra h1
    have h2 : x = 1 := by linarith 
    rw [h2] at h
    simp [Finset.sum_range_succ] at h 
    all_goals
      try { 
        nlinarith 
      }
  
  have eq2 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) * x ^ i = (1 - (n + 1) * x ^ n + n * x ^ (n + 1)) / (1 - x) ^ 2 := by
    intro n 
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      rw [Finset.sum_range_succ, ih]
      field_simp [eq1]
      ring_nf
      <;> field_simp [eq1]
      <;> ring_nf
  specialize eq2 n 
  simpa using eq2