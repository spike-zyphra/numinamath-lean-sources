import Mathlib

open Real Set

theorem inequalities_1142 :
    IsLeast {n : ℝ | ∃ x y z : ℝ, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ n = (y - x)^2 / ((y - z) * (z - x)) +
      (z - y)^2 / ((z - x) * (x - y)) + (x - z)^2 / ((x - y) * (y - z))} 3 := by

  constructor
  · -- Prove that 3 is in the set
    use 0, 1, -1
    norm_num

  · -- Assume n is in the set, we need to show n >= 3
    intro n hn
    rcases hn with ⟨x, y, z, hxy, hxz, hyz, hn⟩

    have h1 : (y - x)^2 / ((y - z) * (z - x)) + (z - y)^2 / ((z - x) * (x - y)) + (x - z)^2 / ((x - y) * (y - z)) = 3 := by
      have h11 : x - y ≠ 0 := by
        intro h
        apply hxy
        linarith
      have h12 : x - z ≠ 0 := by
        intro h
        apply hxz
        linarith
      have h13 : y - z ≠ 0 := by
        intro h
        apply hyz
        linarith
      have h4 : y - x ≠ 0 := by
        intro h
        apply hxy
        linarith
      have h5 : z - x ≠ 0 := by
        intro h
        apply hxz
        linarith
      have h6 : z - y ≠ 0 := by
        intro h
        apply hyz
        linarith
      field_simp [(show y - z ≠ 0 by assumption), (show z - x ≠ 0 by assumption), (show x - y ≠ 0 by assumption),
          (show y - x ≠ 0 by assumption), (show z - y ≠ 0 by assumption), (show x - z ≠ 0 by assumption)]
      ring

    linarith [h1, hn]