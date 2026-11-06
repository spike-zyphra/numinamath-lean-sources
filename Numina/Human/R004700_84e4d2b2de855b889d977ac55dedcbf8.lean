import Mathlib

theorem algebra_305239 :
    IsLeast {y | ∃ x : ℝ, y = abs (x - 1) + abs (x + 1) + abs (x + 5)} 6 := by
  constructor
  · -- $6 \in \{y \mid \exists x \in \mathbb{R}, y = |x-1| + |x+1| + |x+5|\}$
    use -1
    norm_num
  · -- $\forall y \in \{y \mid \exists x \in \mathbb{R}, y = |x-1| + |x+1| + |x+5|\}, y \geq 6$
    intro y hy
    rcases hy with ⟨x, hx⟩
    by_cases h1 : x ≥ 1
    · -- $x \geq 1$
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hx
      linarith
    by_cases h2 : x ≥ -1
    · -- $-1 \leq x < 1$
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hx
      linarith
    by_cases h3 : x ≥ -5
    · -- $-5 \leq x < -1$
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at hx
      linarith
    · -- $x < -5$
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hx
      linarith