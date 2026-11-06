import Mathlib

theorem algebra_188227 {x y z : ℝ} (h1 : x ≠ -y) (h2 : y ≠ -z) (h3 : z ≠ -x)
    (h4 : x * y * z / (x + y) = 6 / 5) (h5 : x * y * z / (y + z) = 2) (h6 : x * y * z / (z + x) = 3 / 2) :
    (x = 3 ∧ y = 2 ∧ z = 1) ∨ (x = -3 ∧ y = -2 ∧ z = -1) := by
  have h7 : x + y ≠ 0 := by
    intro h
    apply h1
    linarith
  have h8 : y + z ≠ 0 := by
    intro h
    apply h2
    linarith
  have h9 : z + x ≠ 0 := by
    intro h
    apply h3
    linarith
  have h7' : x * y * z = 6 / 5 * (x + y) := by 
    have h7ne : x + y ≠ 0 := h7
    field_simp [h7ne] at h4 ⊢
    linarith
  have h8' : x * y * z = 2 * (y + z) := by 
    have h8ne : y + z ≠ 0 := h8
    field_simp [h8ne] at h5 ⊢
    linarith
  have h9' : x * y * z = 3 / 2 * (z + x) := by 
    have h9ne : z + x ≠ 0 := h9
    field_simp [h9ne] at h6 ⊢
    linarith
  
  have h10 : x * y * z ≠ 0 := by 
    by_contra h
    rw [h] at h4 h5 h6
    field_simp [h7, h8, h9] at h4 h5 h6
    all_goals linarith

  have eq4 : 3 * x - 2 * y - 5 * z = 0 := by
    have eq4 : (6 / 5) * (x + y) = 2 * (y + z) := by
      linarith [h7', h8']
    have eq5 : 6 * (x + y) = 10 * (y + z) := by
      linarith [eq4]
    linarith [eq5]

  have eq7 : x - 4 * y + 5 * z = 0 := by
    have eq6 : (6 / 5) * (x + y) = (3 / 2) * (z + x) := by
      linarith [h7', h9']
    have eq7 : 12 * (x + y) = 15 * (z + x) := by
      linarith [eq6]
    nlinarith

  have eq8 : y = 2 * z := by
    nlinarith [eq4, eq7]
  
  have eq9 : x = 3 * z := by
    nlinarith [eq7, eq8]

  have eq10 : x * y * z = 6 * z ^ 3 := by 
    rw [show x = 3 * z by linarith [eq9], show y = 2 * z by linarith [eq8]]
    ring

  have eq11 : 6 * z ^ 3 = 6 * z := by
    nlinarith [show x * y * z = 6 * z ^ 3 by linarith [eq10], h8']

  have h14 : z ≠ 0 := by 
    by_contra h
    have h15 : z = 0 := by linarith 
    have h16 : x = 0 := by 
      linarith [eq9, h15]
    have h17 : y = 0 := by 
      linarith [eq8, h15]
    have h18 : x * y * z = 0 := by 
      simp [h16, h17, h15]
    contradiction

  have h15 : z ^ 2 = 1 := by 
    apply (mul_left_inj' h14).mp
    nlinarith
  have h99 : z = 1 ∨ z = -1 := by
    rw [sq_eq_one_iff] at h15
    tauto
  cases h99 with
  | inl hz =>
    have hx : x = 3 := by 
      linarith [eq9, hz]
    have hy : y = 2 := by 
      linarith [eq8, hz]
    left
    exact ⟨hx, hy, hz⟩

  | inr hz =>
    have hx : x = -3 := by 
      linarith [eq9, hz]
    have hy : y = -2 := by 
      linarith [eq8, hz]
    right
    exact ⟨hx, hy, hz⟩