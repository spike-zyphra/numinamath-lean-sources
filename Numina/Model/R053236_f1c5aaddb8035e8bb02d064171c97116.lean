import Mathlib

theorem algebra_228627 {x : ℝ} (hx : x ≠ 0) (h : 240 / (x * 0.8) = 270 / x + 1) :
    x = 30 := by
  have h1 : x * 0.8 ≠ 0 := by
    intro h2
    apply hx
    have h3 : x * 0.8 = 0 := by linarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · linarith
    · norm_num at h5 ⊢
      all_goals linarith
  have eq1 : 240 / (x * 0.8) = 300 / x := by
    have h2 : x ≠ 0 := hx
    field_simp [h1, h2]
    <;> ring_nf <;> norm_num <;> nlinarith
  rw [eq1] at h
  have eq2 : 300 / x - 270 / x = 1 := by
    linarith 
  have eq3 : 30 / x = 1 := by
    have : 300 / x - 270 / x = 30 / x := by
      field_simp [hx]
      <;> linarith 
    rw [this] at eq2 
    linarith 
  have eq4 : x = 30 := by
    field_simp [hx] at eq3 
    linarith 
  exact eq4