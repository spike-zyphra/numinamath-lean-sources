import Mathlib

open Real

theorem other_286444 {A B : ℝ} (hA : A > 0) (hB : B > 0)
    (hAB : A * B > 0) (h : A * (1 / 3) = B * (2 / 3)) :
    (A * (1 / 3)) / (A * (1 / 3) + B * (2 / 3)) = 1 / 2 := by
        have h1 : A = 2 * B := by
            linarith
        rw [h1]
        field_simp
        ring