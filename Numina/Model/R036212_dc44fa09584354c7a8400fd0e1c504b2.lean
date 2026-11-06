import Mathlib

theorem algebra_165237 {a r : ℤ} (hr : r ≠ 0) (h : a + ar + ar^2 = 91)
    (h' : ∃ d, a + 25 = a + d ∧ a + ar + 27 = a + 2 * d ∧ a + ar^2 + 1 = a + 3 * d) :
    a * r^6 = 5103 := by 
  rcases h' with ⟨d, h1, h2, h3⟩
  have eq1 : d = 25 := by
    linarith
  have eq2 : a * r = 23 := by
    rw [eq1] at h2
    nlinarith
  have eq3 : a * r^2 = 74 := by
    rw [eq1] at h3
    nlinarith
  have eq4 : 23 * r = 74 := by
    calc
      23 * r = (a * r) * r := by 
        rw [eq2]
      _ = a * r^2 := by 
        ring
      _ = 74 := eq3
  omega