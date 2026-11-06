import Mathlib

open Real

theorem calculus_22705 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne1 : x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1) :
    Matrix.det (fun i j : Fin 3 => if i = j then 1 else if i = 0 ∧ j = 1 then logb x y else if i = 0 ∧ j = 2 then logb x z else if i = 1 ∧ j = 0 then logb y x else if i = 1 ∧ j = 1 then 1 else if i = 1 ∧ j = 2 then logb y z else if i = 2 ∧ j = 0 then logb z x else if i = 2 ∧ j = 1 then logb z y else 1) = 0 := by
  have hx1 : x ≠ 1 := hne1.1
  have hy1 : y ≠ 1 := hne1.2.1
  have hz1 : z ≠ 1 := hne1.2.2
  simp [Matrix.det_fin_three, Fin.sum_univ_three, Fin.sum_univ_two, logb]
  have h1 : log x ≠ 0 := by
    by_contra h
    have : x = 1 := by
      have h1 : log x = 0 := by
        simpa using h
      rw [log_eq_zero] at h1
      rcases h1 with (r | r | r)
      · linarith
      · linarith
      · linarith
    contradiction
  have h2 : log y ≠ 0 := by
    by_contra h
    have : y = 1 := by
      have h1 : log y = 0 := by
        simpa using h
      rw [log_eq_zero] at h1
      rcases h1 with (r | r | r)
      · linarith
      · linarith
      · linarith
    contradiction
  have h3 : log z ≠ 0 := by
    by_contra h
    have : z = 1 := by
      have h1 : log z = 0 := by
        simpa using h
      rw [log_eq_zero] at h1
      rcases h1 with (r | r | r)
      · linarith
      · linarith
      · linarith
    contradiction
  field_simp [h1, h2, h3]
  <;> ring