import Mathlib

open Real

theorem algebra_306317 {q : ℝ} (hq : q ≠ 0) (h : ∀ n : ℕ, ∑ i in Finset.range n, (q ^ i) > 0) :
    q ∈ Set.Ioo (-1) 0 ∪ Set.Ioi 0 := by 
  have h0 := h 0
  simp at h0