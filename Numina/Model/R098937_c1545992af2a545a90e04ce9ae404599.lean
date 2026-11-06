import Mathlib

theorem algebra_138243 (x : Fin 3 → ℝ)
    (h1 : 2*x 0+7*x 1+13*x 2=0)
    (h2 : 3*x 0+14*x 1+12*x 2=18)
    (h3 : 5*x 0+25*x 1+16*x 2=39) :
    x 0=-4 ∧ x 1=3 ∧ x 2=-1 := by
  have h4 : 7 * x 1 - 15 * x 2 = 36 := by
    linarith [h1, h2]

  have h5 : 15 * x 1 - 33 * x 2 = 78 := by
    linarith [h1, h3]

  have hx2 : x 2 = -1 := by
    linarith [h4, h5]

  have hx1 : x 1 = 3 := by 
    linarith [h4, hx2]

  have hx0 : x 0 = -4 := by
    linarith [h1, hx1, hx2]

  exact ⟨hx0, hx1, hx2⟩