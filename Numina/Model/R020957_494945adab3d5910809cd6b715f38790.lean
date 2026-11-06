import Mathlib

theorem algebra_233763 {x y : ℝ} (hx : ¬∃ n : ℤ, x = n) (h1 : y = 2 * ⌊x⌋ + 3)
    (h2 : y = 3 * ⌊x - 2⌋ + 5) :
    15 < x + y ∧ x + y < 16 := by

  have h3 : ⌊x - 2⌋ = ⌊x⌋ - 2 := by 
    -- express [x - 2] in terms of [x]
    have h4 : ⌊x - 2⌋ = ⌊x⌋ - 2 := by
      simp [Int.floor_sub_int]
      <;> norm_num
    exact h4

  have h4 : (↑⌊x⌋ : ℝ) = 4 := by
    have eq2 : (y : ℝ) = 3 * (↑⌊x - 2⌋ : ℝ) + 5 := by
      simpa using h2
    have eq3 : (↑⌊x - 2⌋ : ℝ) = (↑⌊x⌋ : ℝ) - 2 := by
      have h9' : ⌊x - 2⌋ = ⌊x⌋ - 2 := h3
      exact_mod_cast h9'
    rw [h1] at eq2
    rw [eq3] at eq2
    nlinarith

  have h5 : ⌊x⌋ = 4 := by 
    exact_mod_cast h4

  have hy : y = 11 := by
    rw [h1]
    rw [show (↑⌊x⌋ : ℝ) = (4 : ℝ) by exact_mod_cast h5]
    norm_num

  -- Compute bounds for x.
  have h8 : (4 : ℝ) ≤ x := by
    have h9 : (↑⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    rw [show (↑⌊x⌋ : ℝ) = (4 : ℝ) by exact_mod_cast h5] at h9
    linarith

  -- Compute upper bound for x.
  have h9 : x < (5 : ℝ) := by
    have h10 : x < (↑⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    rw [show (↑⌊x⌋ : ℝ) = (4 : ℝ) by exact_mod_cast h5] at h10
    linarith

  -- Show that x must be strictly greater than 4
  have h11 : 4 < x := by 
    by_contra h
    push_neg at h
    have h12 : x = (4 : ℝ) := by linarith
    -- This contradicts with the fact that x is not an integer
    exfalso 
    apply hx
    refine' ⟨4, by 
      norm_num [h12]⟩

  -- Compute x + y bounds
  constructor
  · -- Prove 15 < x + y
    rw [hy]
    linarith
  · -- Prove x + y < 16
    rw [hy]
    linarith