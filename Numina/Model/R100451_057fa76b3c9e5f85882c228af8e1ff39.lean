import Mathlib

theorem algebra_281289 (x : Fin 5 → ℕ) (hx : x 0 = 150 ∧ x 1 = 200 ∧ x 2 = 250 ∧ x 3 = 300 ∧ x 4 = 350) :
    (x 0 + x 1 + x 2 + x 3 + x 4) / 5 ∈ Finset.Ioo 200 300 := by 
  rcases hx with ⟨hx0, hx1, hx2, hx3, hx4⟩
  have h1 : x 0 = 150 := hx0
  have h2 : x 1 = 200 := hx1
  have h3 : x 2 = 250 := hx2
  have h4 : x 3 = 300 := hx3
  have h5 : x 4 = 350 := hx4
  have h6 : (x 0 + x 1 + x 2 + x 3 + x 4) / 5 = 250 := by
    simp [h1, h2, h3, h4, h5]
    <;> try { norm_num }
  rw [h6]
  exact Finset.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩