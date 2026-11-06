import Mathlib

theorem algebra_15958 (c : ℝ) (h : ∃ a b, ∀ x, x ^ 2 + 100 * x + c = (a + b * x) ^ 2) :
    c = 2500 := by
  rcases h with ⟨a, b, h_eq⟩
  have eq1 := h_eq 0
  have eq2 : c = a ^ 2 := by
    nlinarith
  have eq5 := h_eq 1
  have eq6 := h_eq (-1)
  ring_nf at eq5 eq6 eq1
  have eq7 : b ^ 2 = 1 := by
    nlinarith
  have eq8 : b = 1 ∨ b = -1 := by
    have h1 : b ^ 2 = 1 := eq7
    rw [sq_eq_one_iff] at h1
    tauto
  have eq9 : 2 * a * b = 100 := by
    nlinarith [eq7, eq1]
  cases eq8 with
  | inl hb1 =>
    have eq10 : a = 50 := by
      rw [hb1] at eq9
      nlinarith
    nlinarith [eq1, eq10]
  | inr hb1 =>
    have eq11 : a = -50 := by
      rw [hb1] at eq9
      nlinarith
    nlinarith [eq1, eq11]