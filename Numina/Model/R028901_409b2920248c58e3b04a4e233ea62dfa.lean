import Mathlib

theorem algebra_277687 (n c : ℝ) (hn : 0 < n) (hc : 0 < c ∧ c ≠ 100)
    (h : ∀ x, 0 < x → (1 + n / 100) * (1 - c / 100) * x = x) :
    n^2 / c^2 = (100 + n) / (100 - c) := by
  have eq1 := h 1 (show 0 < (1 : ℝ) by linarith)
  have eq2 : (1 + n / 100) * (1 - c / 100) = 1 := by
    linarith
  have eq3 : 100 * n = 100 * c + n * c := by
    field_simp at eq2 ⊢
    nlinarith
  have eq4 : 100 * n = c * (100 + n) := by
    linarith
  have hc1 : 0 < c := hc.1
  have hc2 : c ≠ 100 := hc.2
  have h100n : 100 + n ≠ 0 := by
    linarith
  have h100c : (100 - c) ≠ 0 := by
    intro h_eq
    have h3 : c = 100 := by linarith
    have h4 : c ≠ 100 := hc2
    contradiction
  -- Now establishing the required equality.
  have eq5 : c = (100 * n) / (100 + n) := by
    have h100nne : 100 + n ≠ 0 := by
      linarith
    field_simp [h100nne]
    <;> nlinarith
  have eq7 : n^2 / c^2 = (n / c) ^ 2 := by
    field_simp [show c ≠ 0 by linarith]
    <;> nlinarith
  have eq8 : n / c = (100 + n) / 100 := by
    have eq6 : c = (100 * n) / (100 + n) := eq5
    rw [eq6]
    have hnne : n ≠ 0 := by linarith
    have h100nne : 100 + n ≠ 0 := by
      linarith
    field_simp [hnne, h100nne]
    <;> nlinarith
  have eq9 : n ^ 2 / c ^ 2 = ((100 + n) / 100) ^ 2 := by
    calc
      n ^ 2 / c ^ 2 = (n / c) ^ 2 := by
        field_simp [show c ≠ 0 by linarith]
      _ = ((100 + n) / 100) ^ 2 := by
        rw [eq8]
  have eq10 : (100 + n) / (100 - c) = ((100 + n) / 100) ^ 2 := by
    rw [eq5]
    have h100nne : 100 + n ≠ 0 := by
      linarith
    field_simp [h100nne, show 100 * (100 + n) - 100 * n ≠ 0 by
      nlinarith [show 0 < n by linarith]
    ]
    <;> nlinarith
  rw [eq9, eq10]