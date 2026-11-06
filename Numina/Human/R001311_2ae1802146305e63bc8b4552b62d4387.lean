import Mathlib

/- Compute $(3^{-1}+5^{-1})^{-1}\pmod{31}$. Express your answer as an integer from $0$ to $30$, inclusive. -/
theorem number_theory_23246 : ((3 : ZMod 31)⁻¹ + (5 : ZMod 31)⁻¹)⁻¹ = 29 := by 
  native_decide
  