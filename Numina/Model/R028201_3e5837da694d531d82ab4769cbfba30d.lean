import Mathlib
open Real

theorem algebra_95812 {a b c d x : ℝ} (ha : a ≠ b) (hb : b ≠ 0) (hd : d ≠ 0) (hbx: b + x ≠ 0) (hcd: c - d ≠ 0)
(h : (a + x) / (b + x) = c / d) :
x = (a * d - b * c) / (c - d) := by
  have eq1 : (a + x) * d = c * (b + x) := by
    have hx1 : (a + x) / (b + x) = c / d := h
    field_simp [hbx, hd] at hx1 ⊢
    linarith
  have eq2 : x = (a * d - b * c) / (c - d) := by
    have eq3 : (a + x) * d = c * (b + x) := eq1
    have eq5 : a * d + x * d = c * b + c * x := by 
      linarith
    have eq6 : a * d - c * b = x * (c - d) := by
      linarith
    have eq8 : x = (a * d - b * c) / (c - d) := by
      have eq9 : a * d - b * c = x * (c - d) := by
        linarith
      have hcdne : c - d ≠ 0 := hcd
      field_simp [hcdne]
      linarith
    exact eq8
  exact eq2