import Mathlib

theorem algebra_242786 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : (x + y) / (x * y) = 1) (h2 : (y + z) / (y * z) = 1 / 2) (h3 : (x + z) / (x * z) = 1 / 3) :
    x = 12 / 5 ∧ y = 12 / 7 ∧ z = -12 := by

  have eq1 : 1 / x + 1 / y = 1 := by 
    have h1' : (x + y) / (x * y) = (1 / x + 1 / y) := by
      field_simp [hx, hy]
      <;> ring
    linarith [h1', h1]
  
  have eq2 : 1 / y + 1 / z = 1 / 2 := by 
    have h2' : (y + z) / (y * z) = (1 / y + 1 / z) := by 
      field_simp [hy, hz]
      <;> ring
    linarith [h2', h2]

  have eq3 : 1 / x + 1 / z = 1 / 3 := by 
    have h3' : (x + z) / (x * z) = (1 / x + 1 / z) := by
      field_simp [hx, hz]
      <;> ring
    linarith [h3', h3]

  have ha1 : 1 / x = 5 / 12 := by
    linarith [eq1, eq2, eq3]

  have hx1 : x = 12 / 5 := by
    have hne : x ≠ 0 := hx 
    field_simp at ha1 ⊢
    linarith

  have hb1 : 1 / y = 7 / 12 := by
    nlinarith [eq1, ha1]

  have hy1 : y = 12 / 7 := by
    have hne : y ≠ 0 := hy
    field_simp at hb1 ⊢ 
    linarith

  have hc1 : 1 / z = -1 / 12 := by 
    nlinarith [eq3, ha1]

  have hz1 : z = -12 := by
    have hne : z ≠ 0 := hz 
    field_simp at hc1 ⊢ 
    linarith 

  exact ⟨hx1, hy1, hz1⟩