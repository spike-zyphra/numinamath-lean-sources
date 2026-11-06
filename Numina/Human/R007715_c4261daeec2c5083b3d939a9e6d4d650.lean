import Mathlib

variable (x : ℝ)
variable (m : ℝ)

/- Definition of power function in terms of its exponent -/
def isPowerFunction (f : ℝ → ℝ) : Prop :=
  ∃ (a : ℝ), ∀ x, f x = x^a

/- Our specific function f(x) = (m²-3)x^(2m) -/
noncomputable def f_9352 (m : ℝ) (x : ℝ) : ℝ := (m^2 - 3) * x^(2*m)

/- Given that the function $y=(m^{2}-3)x^{2m}$ concerning $x$ is a power function, find the value of $m=$ _____ . -/
theorem algebra_9352 :
  isPowerFunction (f_9352 m) → m = 2 ∨ m = -2 := by
  intro h
  rcases h with ⟨a, h⟩
  have h1 : ∀ x > 0, (m^2 - 3) * x^(2*m) = x^a := by
    intro x hx
    exact h x
  -- For x = 1, we get m^2 - 3 = 1
  have h2 := h1 1 (by norm_num)
  simp at h2
  -- Therefore m^2 = 4
  have h3 : m^2 = 4 := by
    linarith
  -- Therefore m = ±2
  have h4 : m = 2 ∨ m = -2 := by
    apply mul_self_eq_mul_self_iff.mp
    rw [← pow_two,h3]
    ring
  exact h4
