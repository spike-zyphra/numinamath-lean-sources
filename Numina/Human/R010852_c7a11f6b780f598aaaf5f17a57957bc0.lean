import Mathlib

/- The product of two 2-digit numbers is $3774$. What is the smaller of the two numbers? -/
theorem algebra_16315 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x * y = 3774) : min x y = 51 := by
  norm_num at hx hy hxy <;>
  rcases hx with ⟨h₁, h₂⟩ <;>
  rcases hy with ⟨h₃, h₄⟩ <;>
  interval_cases x <;> interval_cases y <;> omega