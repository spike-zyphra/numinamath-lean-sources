import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15386 {h : ℝ → ℝ} (h_def : h = λ x => 2 * (x + 7) * (x - 3) / (x + 7)) :
    image h {x | x + 7 ≠ 0} = Iio (-20) ∪ Ioi (-20) := by
  have h_eq : ∀ x, x + 7 ≠ 0 → h x = 2 * (x - 3) := by
    intro x hx
    rw [h_def]
    have h1 : x + 7 ≠ 0 := hx
    field_simp [h1]
    all_goals ring

  ext y
  simp only [mem_image, mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
  constructor
  · -- First direction: if y in image h, then y in Iio (-20) ∪ Ioi (-20)
    rintro ⟨x, hx, hxy⟩
    rw [h_eq x hx] at hxy
    by_cases h2 : y < -20
    · -- If y < -20, then y in Iio (-20) ∪ Ioi (-20)
      left
      exact h2
    · -- If ¬(y < -20), then y ≥ -20
      have h3 : y ≥ -20 := by linarith
      have h4 : y > -20 := by
        by_contra h
        push_neg at h
        have h5 : y = -20 := by
          linarith
        have h6 : 2 * (x - 3) = -20 := by
          linarith [h5, hxy]
        have h7 : x = -7 := by
          linarith
        have h8 : x + 7 = 0 := by
          linarith
        contradiction
      right
      linarith
  · -- Second direction: if y in Iio (-20) ∪ Ioi (-20), then y in image h
    rintro (h2 | h3)
    · -- If y < -20
      use (3 + y / 2)
      constructor
      · -- Show x + 7 ≠ 0
        by_contra h
        have h4 : (3 + y / 2) + 7 = 0 := by linarith
        have h5 : y = -20 := by
          linarith
        linarith
      · -- Show h x = y
        rw [h_eq (3 + y / 2) (by
          by_contra h
          have h4 : (3 + y / 2) + 7 = 0 := by linarith
          have h5 : y = -20 := by
            linarith
          linarith
        )
        ]
        linarith
    · -- If y > -20
      use (3 + y / 2)
      constructor
      · -- Show x + 7 ≠ 0
        by_contra h
        have h4 : (3 + y / 2) + 7 = 0 := by linarith
        have h5 : y = -20 := by
          linarith
        linarith
      · -- Show h x = y
        rw [h_eq (3 + y / 2) (by
          by_contra h
          have h4 : (3 + y / 2) + 7 = 0 := by linarith
          have h5 : y = -20 := by
            linarith
          linarith
        )
        ]
        linarith