import Mathlib

theorem algebra_16501 : IsLeast {w : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y + z = 1 ∧ w = 1 / (x + y) + 1 / (x + z) + 1 / (y + z)} (9 / 2) := by
  constructor
  · -- Show that 9/2 is in the set.
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Show that 9/2 is the least element in the set.
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, hsum, hw⟩
    have h7 : 1 / (x + y) + 1 / (x + z) + 1 / (y + z) ≥ 9 / 2 := by
      have h1 : 0 < x + y := by nlinarith
      have h2 : 0 < x + z := by nlinarith
      have h3 : 0 < y + z := by nlinarith 
      have pos1 : 0 < (x + y : ℝ) := by nlinarith 
      have pos2 : 0 < (x + z : ℝ) := by nlinarith 
      have pos3 : 0 < (y + z : ℝ) := by nlinarith 
      have h8 : (1 / (x + y) + 1 / (x + z) + 1 / (y + z)) =
          ((x + z) * (y + z) + (x + y) * (y + z) + (x + y) * (x + z)) / ((x + y) * (x + z) * (y + z)) := by 
        field_simp 
        <;> ring 
      rw [h8] at *
      have h9 : ((x + y) * (x + z) * (y + z)) > 0 := by 
        positivity
      have h10 : ( (x + z) * (y + z) + (x + y) * (y + z) + (x + y) * (x + z) ) ≥ (9 / 2) * ((x + y) * (x + z) * (y + z)) := by
        have h5 : (x + y) + (x + z) + (y + z) = 2 := by 
          nlinarith 
        have h11 : ( (x + z) * (y + z) + (x + y) * (y + z) + (x + y) * (x + z) ) ≥ (9 / 2) * ((x + y) * (x + z) * (y + z)) := by
          nlinarith [sq_nonneg (x + y - (x + z)), sq_nonneg (x + y - (y + z)), sq_nonneg (x + z - (y + z)), 
          sq_nonneg (x + y + x + z + y + z - 2), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x + y by nlinarith) (show 0 < x + z by nlinarith), 
          mul_pos (show 0 < x + y by nlinarith) (show 0 < y + z by nlinarith), 
          mul_pos (show 0 < x + z by nlinarith) (show 0 < y + z by nlinarith)
          ]
        linarith 
      have h12 : ((x + z) * (y + z) + (x + y) * (y + z) + (x + y) * (x + z)) / ((x + y) * (x + z) * (y + z)) ≥ 9 / 2 := by
        apply (le_div_iff₀ (by positivity)).mpr 
        linarith 
      linarith
    linarith [hw, h7]