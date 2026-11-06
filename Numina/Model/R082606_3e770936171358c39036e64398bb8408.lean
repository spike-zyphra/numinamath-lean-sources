import Mathlib

theorem inequalities_45986 (x y : Fin 3 → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hxy : x 0 + y 1 = 1 ∧ x 1 + y 2 = 1 ∧ x 2 + y 0 = 1) :
    x 0 * y 0 + x 1 * y 1 + x 2 * y 2 < 1 := by

  rcases hxy with ⟨h₁, h₂, h₃⟩

  have h1' : y 1 = 1 - x 0 := by linarith
  have h2' : y 2 = 1 - x 1 := by linarith
  have h3' : y 0 = 1 - x 2 := by linarith

  have pos0 : 0 < x 0 := hx 0
  have pos1 : 0 < x 1 := hx 1
  have pos2 : 0 < x 2 := hx 2
  have posy0 : 0 < y 0 := hy 0
  have posy1 : 0 < y 1 := hy 1
  have posy2 : 0 < y 2 := hy 2

  have h4 : x 0 < 1 := by
    nlinarith [h1', posy1]

  have h5 : x 1 < 1 := by
    nlinarith [h2', posy2]

  have h6 : x 2 < 1 := by
    nlinarith [h3', posy0]

  have eq1 : x 0 * y 0 + x 1 * y 1 + x 2 * y 2 =
          x 0 * (1 - x 2) + x 1 * (1 - x 0) + x 2 * (1 - x 1) := by 
        rw [h3', h1', h2']
  
  rw [eq1]

  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 0),
          mul_pos pos0 pos1, mul_pos pos1 pos2, mul_pos pos2 pos0,
          mul_pos (sub_pos.mpr h4) (sub_pos.mpr h5), 
          mul_pos (sub_pos.mpr h5) (sub_pos.mpr h6), 
          mul_pos (sub_pos.mpr h6) (sub_pos.mpr h4)
          ]