import Mathlib

variable (x : ℝ)
variable (m : ℝ)

/- Definition of power function in terms of its exponent -/
def isPowerFunction (f : ℝ → ℝ) : Prop :=
  ∃ (a : ℝ), ∀ x, f x = x^a

/- Our specific function f(x) = (m²-3)x^(2m) -/
noncomputable def f_9352 (m : ℝ) (x : ℝ) : ℝ := (m^2 - 3) * x^(2*m)

theorem algebra_9352 :
  isPowerFunction (f_9352 m) → m = 2 ∨ m = -2 := by
  intro h
  rcases h with ⟨a, ha⟩
  have h1 := ha 1
  simp [f_9352] at h1
  have h2 : m^2 = 4 := by nlinarith
  have h3 : m = 2 ∨ m = -2 := by
    have h4 : m^2 - 4 = 0 := by linarith
    have h5 : (m - 2) * (m + 2) = 0 := by 
      linarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · left
      linarith
    · right
      linarith
  exact h3