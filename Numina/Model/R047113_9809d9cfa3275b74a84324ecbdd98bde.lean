import Mathlib

theorem algebra_11353 (c : ℝ) (h : ∃! x, (2*x + c)^2 = 8*x) :
    c = 1 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have eq1 : 4 * x ^ 2 + (4 * c - 8) * x + c ^ 2 = 0 := by
    nlinarith
  have eq4 : ∀ y, (2 * y + c) ^ 2 = 8 * y → y = x := hx2
  have eq5 : (2 - c - x) = x := by
    have h_eq : (2 * (2 - c - x) + c) ^ 2 = 8 * (2 - c - x) := by
      nlinarith [eq1, sq_nonneg (x - (2 - c) / 2), sq_nonneg ((2 - c - x) - x)]
    have eq6 : (2 - c - x) = x := by
      apply eq4 (2 - c - x) h_eq
    linarith
  have eq6 : 2 * x = 2 - c := by
    linarith [eq5]
  have eq7 : c = 1 := by
    have eq8 : x = (2 - c) / 2 := by
      linarith [eq6]
    rw [eq8] at eq1
    nlinarith
  linarith