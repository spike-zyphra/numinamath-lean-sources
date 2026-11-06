import Mathlib

  theorem algebra_1244 (d c t s : ℝ) (hpos : 0 < d ∧ 0 < c ∧ 0 < t ∧ 0 < s)
  (h0 : d = 15) (h1 : c / s + (d - c) / (s / 4) = d / (s / 2)) :
  c = 10 := by
  rcases hpos with ⟨hd, hc, ht, hs⟩
  have eq1 : c / s + (d - c) / (s / 4) = (4 * d - 3 * c) / s := by
    have h2 : s ≠ 0 := by linarith
    field_simp
    <;> ring
  have eq2 : d / (s / 2) = 2 * d / s := by
    have h3 : s ≠ 0 := by linarith
    field_simp
    <;> ring
  rw [eq1, eq2] at h1
  have h2 : s ≠ 0 := by linarith
  have h3 : 4 * d - 3 * c = 2 * d := by
    have h4 : (4 * d - 3 * c) / s = (2 * d) / s := by
      simpa using h1
    have h5 : (4 * d - 3 * c) / s = (2 * d) / s := h4
    have h6 : 4 * d - 3 * c = 2 * d := by
      field_simp [h2] at h5 ⊢
      <;> linarith
    exact_mod_cast h6
  have h5 : d = 15 := h0
  rw [h5] at h3
  linarith