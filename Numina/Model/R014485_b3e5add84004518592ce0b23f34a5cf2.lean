import Mathlib

def f (x y : ℝ) := x * y

theorem algebra_276580 {f : ℝ → ℝ → ℝ} (h1 : ∀ x, f x x = 5)
    (h2 : ∀ x y z, f x (f y z) = f x y + z - 5) :
    f 2021 1949 = 77 := by
  have h3 : ∀ x, f x 5 = x := by
    intro x
    have eq := h2 x x x
    have hx1 : f x x = 5 := h1 x
    simp [hx1] at eq
    linarith
  have eq1 := h2 2021 1949 1949
  have h4 : f 1949 1949 = 5 := h1 1949
  have eq2 : f 2021 (5 : ℝ) = (2021 : ℝ) := by
    specialize h3 2021
    simpa using h3
  have eq3 : f 2021 (5 : ℝ) = f 2021 1949 + (1944 : ℝ) := by
    have eq4 : f 2021 (f 1949 1949) = f 2021 1949 + (1949 : ℝ) - 5 := by
      simpa using eq1
    rw [h4] at eq4
    linarith
  linarith [eq2, eq3]