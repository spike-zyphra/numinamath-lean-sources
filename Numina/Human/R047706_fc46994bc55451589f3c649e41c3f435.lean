import Mathlib

/- Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. -/
theorem algebra_21389 {V I Z : ℂ} (hV : V = 1 + Complex.I) (hZ : Z = 2 - Complex.I)
    (hOhmsLaw : V = I * Z) : I = 1 / 5 + 3 / 5 * Complex.I := by 
  rw [hV, hZ] at hOhmsLaw
  field_simp [Complex.ext_iff] at hOhmsLaw ⊢
  constructor <;> linarith