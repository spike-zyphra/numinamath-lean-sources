import Mathlib

/- Find the ordered pair $(j,k)$ that satisfies the equations $5j-42k=1$ and $2k-j=3$. -/
theorem algebra_14614 {j k : ℝ} (h₀ : 5 * j - 42 * k = 1) (h₁ : 2 * k - j = 3) :
    j = -4 ∧ k = -1 / 2 := by
  refine' ⟨_, _⟩ <;> linarith