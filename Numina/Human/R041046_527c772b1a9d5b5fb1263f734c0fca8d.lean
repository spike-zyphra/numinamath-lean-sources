import Mathlib

open Real Set
open scoped BigOperators

/- Find the minimum possible value of the largest of $xy$, $1-x-y+xy$, and $x+y-2xy$ if $0\leq x \leq y \leq 1$. -/
theorem algebra_20936 :
  IsLeast {z : ℝ | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 ∧ z = max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y)} (4 / 9) := by 
  refine' ⟨⟨1 / 3, 1 / 3, by norm_num⟩, _⟩
  rintro z ⟨x, y, h, h₀, h₁, h₂⟩
  rw [h₂]
  cases' le_total (x * y) (1 - x - y + x * y) with h h <;>
    cases' le_total (x + y - 2 * x * y) (max (x * y) (1 - x - y + x * y)) with h' h' <;>
      simp_all [max_le_iff] <;>
        nlinarith