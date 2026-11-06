import Mathlib

theorem algebra_168468 (I : Fin 5 → ℝ) (hI : ∀ i, I i > 0)
    (hI1 : I 0 = 2) (hI2 : I 1 = I 0 + I 2) (hI3 : I 2 = I 1 + I 3)
    (hI4 : I 3 = I 2 + I 4) (hI5 : I 4 = I 3 + I 0) :
    I 0 + I 1 + I 2 + I 3 + I 4 = 24 := by
        have hI0 : I 0 > 0 := hI 0
        have hI1' : I 1 > 0 := hI 1
        have hI2' : I 2 > 0 := hI 2
        have hI3' : I 3 > 0 := hI 3
        have hI4' : I 4 > 0 := hI 4
        rw [hI1] at hI2
        have eq1 : I 1 = 2 + I 2 := by linarith
        rw [eq1] at hI3
        have hI3_neg : I 3 < 0 := by linarith
        linarith