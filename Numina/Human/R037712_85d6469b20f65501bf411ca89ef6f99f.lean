import Mathlib

/- Solve for $z$ in the following equation: $2-3iz = 3 + 2iz$. -/
theorem algebra_21891 {z : ℂ} (hz : 2 - 3 * Complex.I * z = 3 + 2 * Complex.I * z) :
    z = Complex.I / 5 := by 
  apply Eq.symm
  rw [Complex.ext_iff] at hz
  field_simp [Complex.ext_iff] at hz ⊢
  constructor <;> linarith