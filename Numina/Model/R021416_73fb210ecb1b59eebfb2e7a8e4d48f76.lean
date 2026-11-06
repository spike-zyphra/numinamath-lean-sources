import Mathlib

theorem algebra_107951 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hseq : ∃ d, b = a + d ∧ c = b + d) (hge1 : ∃ r, (a + 1) * r = b ∧ b * r = c)
    (hge2 : ∃ r, (c + 2) * r = b ∧ b * r = a) : b = 12 := by
  rcases hseq with ⟨d, hb1, hc1⟩
  rcases hge1 with ⟨r1, hge11, hge12⟩
  rcases hge2 with ⟨r2, hge21, hge22⟩
  have eq1 : b ^ 2 = (a + 1) * c := by
    have h1 : r1 = c / b := by
      have hne : b ≠ 0 := hb
      field_simp [hne]
      nlinarith [hge12]
    rw [h1] at hge11
    have hne : b ≠ 0 := hb
    field_simp [hne] at hge11 ⊢
    nlinarith [hge11]
  have eq2 : b ^ 2 = a * (c + 2) := by
    have h2 : r2 = a / b := by
      have hne : b ≠ 0 := hb
      field_simp [hne]
      nlinarith [hge22]
    rw [h2] at hge21
    have hne : b ≠ 0 := hb
    field_simp [hne] at hge21 ⊢
    nlinarith [hge21]
  have eq3 : (a + 1) * c = a * (c + 2) := by
    nlinarith [eq1, eq2]
  have h1 : c = 2 * a := by
    nlinarith [eq3]
  have h2 : d = a / 2 := by
    have h3 : c = b + d := hc1
    have h4 : b = a + d := hb1
    rw [h4] at h3
    nlinarith [h1, h3]
  have h3 : b = 3 / 2 * a := by
    nlinarith [hb1, h2]
  have h4 : b ^ 2 = a * (c + 2) := by
    linarith [eq2]
  rw [show c = 2 * a by linarith [h1]] at h4
  rw [h3] at h4
  have h5 : a * (a - 8) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · 
    exfalso
    apply ha
    linarith
  · 
    have h8 : a = 8 := by linarith
    rw [h8] at h3
    linarith [h3]