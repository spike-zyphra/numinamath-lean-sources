import Mathlib

theorem algebra_2278 {x : ℝ} :
  (x^2 + 3 * x + 1)^2 - 12 * (x^2 + 3 * x) = 1 ↔
  x = 0 ∨ x = -3 ∨ x = -5 ∨ x = 2 := by
  constructor
  · -- (\Rightarrow) If $(x^{2}+3 x+1)^{2}-12(x^{2}+3 x)=1$ then $x\in\{ 0, -3, -5, 2 \}$.
    intro h
    -- Set $y = x^2 + 3x$ to simplify the equation.
    have h1 : (x ^ 2 + 3 * x) * ((x ^ 2 + 3 * x) - 10) = 0 := by
      ring_nf at h ⊢
      linarith
    
    simp at h1
    -- Consider the two cases.
    rcases h1 with h1 | h1
    · -- $x^2 + 3x = 0$:
      have h2 : x * (x + 3) = 0 := by
        ring_nf at h1 ⊢
        linarith
      simp at h2
      -- Consider the two cases.
      rcases h2 with h2 | h2
      · -- $x = 0$:
        simp [h2]
      · -- $x + 3 = 0$ so $x = -3$:
        have h3 : x = -3 := by linarith
        simp [h3]
    · -- $y = 10$, so $x^2 + 3 x = 10$ leads to $x^2 + 3x -10 = 0$:
      have h2 : (x - 2) * (x + 5) = 0 := by 
        ring_nf at h1 ⊢
        linarith
      simp at h2
      -- Consider the two cases.
      rcases h2 with h2 | h2
      · -- $x - 2 = 0$ leads to $x = 2$:
        have h3 : x = 2 := by linarith
        simp [h3]
      · -- $x + 5 = 0$ leads to $x = -5$:
        have h3 : x = -5 := by linarith
        simp [h3]
  · -- (\Leftarrow) If $x\in\{ 0, -3, -5, 2 \}$ then $(x^{2}+3 x+1)^{2}-12(x^{2}+3 x)=1$.
    intro h
    rcases h with h | h | h | h
    · -- x = 0
      rw [h]
      norm_num
    · -- x = -3
      rw [h]
      norm_num
    · -- x = -5
      rw [h]
      norm_num
    · -- x = 2
      rw [h]
      norm_num