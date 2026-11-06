import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12091 {f : ℝ → ℝ} (hf : f = λ x => (x^2 + 3 * x + 2) / (x + 1)) :
    image f {x | x + 1 ≠ 0} = Iio 1 ∪ Ioi 1 := by 
  ext y
  simp only [hf, Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume y in image of f
    rintro ⟨x, hx, rfl⟩
    have h1 : x + 1 ≠ 0 := hx
    have eq1 : (x ^ 2 + 3 * x + 2) / (x + 1) = x + 2 := by
      have h2 : x + 1 ≠ 0 := h1
      field_simp [h2]
      <;> ring
    rw [eq1] at *
    by_cases h2 : x + 2 < (1 : ℝ)
    · -- Case 1: x + 2 < 1, so y < 1
      left
      linarith
    · -- Case 2: x + 2 ≥ 1
      by_cases h3 : x + 2 > (1 : ℝ)
      · -- Case 2a: x + 2 > 1, so y > 1
        right
        linarith
      · -- Case 2b: x + 2 = 1
        have h4 : x + 2 = 1 := by linarith
        -- This leads to a contradiction
        have h5 : x = -1 := by linarith
        have h6 : x + 1 = 0 := by
          rw [h5]
          norm_num
        contradiction
  · -- Show that any y in (-∞,1)∪(1,∞) is attained
    rintro (h | h)
    · -- Case y < 1
      use (y - 2)
      constructor
      · -- Show x + 1 ≠ 0
        by_contra h3
        have h4 : y = 1 := by
          nlinarith
        linarith
      · -- Show f(x) = y
        field_simp [(show (y - 2 : ℝ) + 1 ≠ 0 by
          by_contra h3
          have h4 : y = 1 := by
            nlinarith
          linarith
        )
        ]
        <;> ring_nf <;> linarith
    · -- Case y > 1
      use (y - 2)
      constructor
      · -- Show x + 1 ≠ 0
        by_contra h3
        have h4 : y = 1 := by
          nlinarith
        linarith
      · -- Show f(x) = y
        field_simp [(show (y - 2 : ℝ) + 1 ≠ 0 by
          by_contra h3
          have h4 : y = 1 := by
            nlinarith
          linarith
        )
        ]
        <;> ring_nf <;> linarith