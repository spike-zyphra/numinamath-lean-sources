import Mathlib

/- What is the least integer value of $x$ such that  $\lvert2x+ 7\rvert\le 16$? -/
theorem algebra_12385 : IsLeast {x : ℤ | abs (2 * x + 7) ≤ 16} (-11) := by 
  refine' ⟨_, fun x => _⟩ <;> simp [abs_le] <;> omega