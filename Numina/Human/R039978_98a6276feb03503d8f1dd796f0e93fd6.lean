import Mathlib

/- Find all sequences of positive integers $a_1,a_2,\dots$ such that $$(n^2+1)a_n = n(a_{n^2}+1)$$ for all positive integers $n$. -/
theorem number_theory_40803 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h : ∀ n, (n ^ 2 + 1) * a n = n * (a (n ^ 2) + 1)) :
    ∀ n, a n = n := by 
  intro n
  have h₀ := h n
  have h₁ := h 0
  simp at h₀ h₁
  linarith [ha 0]