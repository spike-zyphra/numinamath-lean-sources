import Mathlib

/- I pick two whole numbers $x$ and $y$ between $1$ and $10$ inclusive (not necessarily distinct). My friend picks two numbers $x -4$ and $2y-1$. If the product of my friend's numbers is one greater than the product of my numbers, then what is the product of my numbers? -/
theorem algebra_20396 {x y : ℤ} (hx : x ∈ Finset.Icc 1 10) (hy : y ∈ Finset.Icc 1 10)
    (h : (x - 4) * (2 * y - 1) = x * y + 1) :
    x * y = 54 := by
  revert x y h
  simp only [Finset.mem_Icc]
  rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩ h5
  interval_cases x <;> interval_cases y <;> omega