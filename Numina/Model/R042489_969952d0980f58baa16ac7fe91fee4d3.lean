import Mathlib

theorem number_theory_5803 (a₁ a₂ : ℤ) :
  a₁.lcm a₂ * a₁.gcd a₂ = |a₁ * a₂| := by
  have h := Int.gcd_mul_lcm a₁ a₂
  rw [mul_comm] at h
  linarith