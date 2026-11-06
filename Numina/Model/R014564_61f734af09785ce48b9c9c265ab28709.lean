import Mathlib

theorem algebra_172862 {b c : ℤ} (h : ∃ x y, x ≠ y ∧ x^2 + b * x + c = 0 ∧ y^2 + b * y + c = 0 ∧ x = 98 ∧ y = 99) :
    {x | 0 ≤ x ∧ x ≤ 100 ∧ 6 ∣ (x^2 + b * x + c)}.ncard = 67 := by
  obtain ⟨x, y, hxy, hx1, hy1, hx2, hy2⟩ := h
  rw [hx2] at hx1
  rw [hy2] at hy1
  have eq1 : 98 ^ 2 + b * 98 + c = 0 := by
    simpa using hx1
  have eq2 : 99 ^ 2 + b * 99 + c = 0 := by
    simpa using hy1
  have eq3 : b = -197 := by
    nlinarith [eq1, eq2]
  have eq4 : c = 9702 := by
    rw [eq3] at eq1
    linarith
  have h1 : b = -197 := eq3
  have h2 : c = 9702 := eq4
  have h3 : {x | 0 ≤ x ∧ x ≤ 100 ∧ 6 ∣ (x^2 + b * x + c)} = Finset.filter (fun x : ℤ => 0 ≤ x ∧ x ≤ 100 ∧ 6 ∣ (x^2 + b * x + c)) (Finset.Icc (0 : ℤ) 100) := by
    ext x
    simp
    <;> omega
  rw [h3]
  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  native_decide