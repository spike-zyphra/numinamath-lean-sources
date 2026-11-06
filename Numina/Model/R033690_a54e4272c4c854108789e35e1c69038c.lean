import Mathlib

theorem algebra_7476 : ∀ z : ℂ, Complex.abs (-(7 + Complex.I - 2 * z)) = 4 ↔
    Complex.abs (2 * z - 7 - Complex.I) = 4 := by 
  intro z 
  have h1 : Complex.abs (-(7 + Complex.I - 2 * z)) = Complex.abs (2 * z - 7 - Complex.I) := by
    have h2 : -(7 + Complex.I - 2 * z) = 2 * z - 7 - Complex.I := by
      ring_nf
    rw [h2]
  rw [h1]
  all_goals 
    simp
  all_goals 
    try { tauto }