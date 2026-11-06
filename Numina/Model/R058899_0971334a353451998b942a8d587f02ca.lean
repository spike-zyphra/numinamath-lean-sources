import Mathlib

theorem algebra_97406 (a : ℕ → ℝ) (h : ∀ n, 0 < n → (Finset.sum (Finset.range n) fun i => a i) / n = n) :
    a 2007 = 4015 := by

  have h1 : ∀ n : ℕ, 0 < n → Finset.sum (Finset.range n) (fun i => a i) = (n : ℝ) * n := by
    intro n hn
    have h2 := h n hn
    field_simp at h2 ⊢
    nlinarith
  
  have h2008 : Finset.sum (Finset.range 2008) (fun i => a i) = (2008 : ℝ) * 2008 := by
    apply h1 2008 (by norm_num)
    
  have h2007 : Finset.sum (Finset.range 2007) (fun i => a i) = (2007 : ℝ) * 2007 := by
    apply h1 2007 (by norm_num)

  have eq1 : a 2007 = Finset.sum (Finset.range 2008) (fun i => a i) - Finset.sum (Finset.range 2007) (fun i => a i) := by
    rw [Finset.sum_range_succ]
    all_goals ring
  
  rw [eq1]
  rw [h2008, h2007]
  norm_num