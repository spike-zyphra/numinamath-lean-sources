import Mathlib

theorem algebra_289792 :
  {(x, y) : ℝ × ℝ | 0 < x ∧ 0 < y ∧ 
   (2 * y) / (x + y) = (3 * x - 2 * y) / (3 * x) ∧
   (2 * y) / 3 + (3 * x * y - 2 * y^2) / (3 * x) = (x * y) / (x + y) + 2} =
  {(6, 3)} := by 
  ext ⟨x, y⟩ 
  simp 
  constructor 
  · -- Assume (x, y) is in the set
    rintro ⟨hx, hy, h1, h2⟩
    have eq3 : 2 * y * (3 * x) = (3 * x - 2 * y) * (x + y) := by 
      have eq2 : (2 * y) / (x + y) = (3 * x - 2 * y) / (3 * x) := h1 
      have h3 : (x + y) ≠ 0 := by nlinarith 
      have h4 : (3 * x) ≠ 0 := by nlinarith 
      field_simp [h3, h4] at eq2 ⊢ 
      nlinarith 
    have eq4 : 5 * x * y - 3 * x ^ 2 + 2 * y ^ 2 = 0 := by 
      nlinarith 
    have eq6 : 2 * x ^ 2 * y + 3 * x * y ^ 2 - 2 * y ^ 3 - 6 * x ^ 2 - 6 * x * y = 0 := by
      have eq5 : (2 * y) / 3 + (3 * x * y - 2 * y^2) / (3 * x) = (x * y) / (x + y) + 2 := h2 
      have eq7 : x ≠ 0 := by nlinarith 
      have eq8 : x + y ≠ 0 := by nlinarith
      field_simp [eq7, eq8] at eq5 ⊢
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
    have eq7 : 3 * x ^ 2 - 5 * x * y - 2 * y ^ 2 = 0 := by 
      nlinarith 
    have eq8 : (x - 2 * y) * (3 * x + y) = 0 := by 
      nlinarith [eq7]
    cases' (mul_eq_zero.1 eq8) with h8 h9
    · -- Case x - 2 * y = 0
      have eq9 : x = 2 * y := by 
        linarith 
      rw [show x = 2 * y by linarith] at eq6 
      have eq10 : 12 * y ^ 2 * (y - 3) = 0 := by
        ring_nf at eq6 ⊢
        nlinarith 
      cases' (mul_eq_zero.1 eq10) with h34 h56
      · -- Case 12 * y ^ 2 = 0
        nlinarith [show 0 < y by linarith] 
      · -- Case y - 3 = 0
        have eq11 : y = 3 := by 
          linarith 
        have eq12 : x = 6 := by 
          nlinarith [eq9, eq11] 
        simp [eq12, eq11]
    · -- Case 3 * x + y = 0
      nlinarith [show 0 < y by linarith, show 0 < x by linarith] 
  · -- Show (6, 3) is in the set
    rintro ⟨rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · norm_num