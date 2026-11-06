import Mathlib

theorem algebra_183084 (x : ℝ) (hx : ⌊(x + 4) / 10⌋ = 5) :
    ⌊(6 * x) / 5⌋ ≤ 67 := by
  have h1 : 5 ≤ (x + 4) / 10 := by
    have h1 : ⌊(x + 4) / 10⌋ = 5 := hx
    have h2 : (5 : ℝ) ≤ (x + 4) / 10 := by
      have h3 : (⌊(x + 4) / 10⌋ : ℝ) ≤ (x + 4) / 10 := by
        exact Int.floor_le ((x + 4) / 10)
      have h4 : (⌊(x + 4) / 10⌋ : ℝ) = (5 : ℝ) := by
        rw [h1]
        <;> norm_num
      linarith
    linarith
  have h2 : (x + 4) / 10 < 6 := by
    have h1 : ⌊(x + 4) / 10⌋ = 5 := hx
    have h3 : (x + 4) / 10 < (⌊(x + 4) / 10⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one ((x + 4) / 10)
    have h4 : (⌊(x + 4) / 10⌋ + 1 : ℝ) = (6 : ℝ) := by
      rw [h1]
      norm_num
    linarith
  have h3 : 46 ≤ x := by
    linarith
  have h4 : x < 56 := by
    linarith
  have h5 : (6 * x) / 5 < 67.2 := by
    linarith
  have h6 : ⌊(6 * x) / 5⌋ ≤ 67 := by
    by_contra h
    push_neg at h
    have h9 : ⌊(6 * x) / 5⌋ ≥ 68 := by 
      omega
    have h10 : (6 * x) / 5 ≥ (68 : ℝ) := by
      have h11 : (⌊(6 * x) / 5⌋ : ℝ) ≤ (6 * x) / 5 := by
        exact Int.floor_le ((6 * x) / 5)
      have h12 : (⌊(6 * x) / 5⌋ : ℝ) ≥ (68 : ℝ) := by
        exact_mod_cast h9
      linarith
    nlinarith
  exact_mod_cast h6