import Mathlib

theorem number_theory_327213 (α β : ℝ) (h : ¬∃ m : ℤ, α ≤ m ∧ m ≤ β) :
    ∃ n : ℕ, 0 < n ∧ ¬∃ m : ℤ, n * α ≤ m ∧ m ≤ n * β ∧ (n * β - n * α) ≥ 1 / 6 := by
  use 1
  constructor
  · -- Show that $1 > 0$.
    norm_num
  · -- Show that there does not exist an integer $m$ in $[1 \cdot \alpha, 1 \cdot \beta]$ with length $\geq \frac{1}{6}$.
    intro h1
    rcases h1 with ⟨m, hm1, hm2, hm3⟩
    have h3 : (α ≤ (↑m : ℝ) ) := by
      simpa using hm1
    have h4 : (↑m : ℝ) ≤ β := by 
      simpa using hm2
    have h5 : ∃ m : ℤ, α ≤ (↑m : ℝ) ∧ (↑m : ℝ) ≤ β := by
      refine ⟨m, ?_⟩
      constructor
      · linarith [h3]
      · linarith [h4]
    have h6 : ¬(∃ m : ℤ, α ≤ (↑m : ℝ) ∧ (↑m : ℝ) ≤ β) := h
    exfalso 
    exact h6 h5