import Mathlib

theorem algebra_195570 {x : ℂ} (hx : x^2 + x + 1 = 0) (a : ℂ) (ha : a = x^4 + x^(-4 : ℤ)) :
    a = -1 := by
  have hx2 : x^2 = -x - 1 := by
    calc
      x^2 = x^2 + x + 1 - x - 1 := by ring
      _ = 0 - x - 1 := by rw [hx]
      _ = -x - 1 := by ring
  have hx3 : x^3 = 1 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-x - 1) := by rw [hx2]
      _ = -x^2 - x := by ring
      _ = -(-x - 1) - x := by rw [hx2]
      _ = x + 1 - x := by ring_nf
      _ = 1 := by ring_nf
  have hx4 : x^4 = x := by 
    calc
      x^4 = x^3 * x := by ring
      _ = 1 * x := by rw [hx3]
      _ = x := by ring
  have hxneg4 : x^(-4 : ℤ) = x⁻¹ := by
    have h1 : x^3 = 1 := by 
      simpa using hx3
    have h2 : x^4 = x := by
      simpa using hx4
    have h3 : x^(-4 : ℤ) = (x^4)⁻¹ := by
      simp [zpow_neg, zpow_ofNat]
    rw [h3, h2]
  rw [ha, hx4, hxneg4]
  have hxne0 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    simp at hx
  have eq1 : x + x ^ 2 = -1 := by
    have eq2 : x^2 + x + 1 = 0 := by
      simpa using hx
    have eq3 : x^2 + x = -1 := by
      calc
        x^2 + x = (x^2 + x + 1) - 1 := by ring
        _ = 0 - 1 := by rw [eq2]
        _ = -1 := by ring
    calc
      x + x^2 = x^2 + x := by ring
      _ = -1 := by rw [eq3]
  have h6 : x * x = x ^ 2 := by ring
  field_simp [hxne0, eq1] at *
  <;> ring_nf at hx ⊢
  <;> norm_num [Complex.ext_iff, hx2] at *