import Mathlib

theorem algebra_296542 {a : ℝ} (ha : a^2 - 14 * a + 1 = 0) :
    (Nat.floor ((a^4 + 1 / a^4) / 10)) % 10 = 3 := by
  have ha2 : a ≠ 0 := by 
    by_contra h
    rw [h] at ha 
    nlinarith
  have ha3 : a + 1 / a = 14 := by 
    have h1 : a ≠ 0 := ha2
    field_simp at *
    nlinarith
  have ha4 : a^2 + 1 / a^2 = 194 := by
    have h1 : a + 1 / a = 14 := ha3 
    have h2 : a^2 + 1 / a^2 = (a + 1 / a)^2 - 2 := by 
      field_simp 
      <;> nlinarith 
    rw [h2, h1] 
    norm_num 
  have ha5 : a^4 + 1 / a^4 = (a^2 + 1 / a^2)^2 - 2 := by 
    field_simp 
    <;> nlinarith 
  have ha6 : a^4 + 1 / a^4 = 37634 := by
    rw [ha5, ha4] 
    norm_num 
  have h1 : (a^4 + 1 / a^4) / 10 = (37634 : ℝ) / 10 := by
    rw [ha6] 
  have h2 : Nat.floor ((a^4 + 1 / a^4) / 10) = 3763 := by
    rw [h1] 
    norm_num [Nat.floor_eq_iff] 
  calc 
    (Nat.floor ((a^4 + 1 / a^4) / 10)) % 10 = 3763 % 10 := by
      rw [h2] 
    _ = 3 := by norm_num