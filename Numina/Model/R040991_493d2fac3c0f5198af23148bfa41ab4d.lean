import Mathlib

theorem algebra_13352 :
    IsGreatest {x : ℝ | x ≠ 0 ∧ ⌊x⌋ / x = 9 / 10} (80 / 9 : ℝ) := by
  constructor
  · -- First, prove that 80/9 is in the set.
    constructor
    · -- Show 80/9 ≠ 0
      norm_num
    · -- Show ⌊80 / 9⌋ / (80 / 9) = 9 / 10
      have h1 : ⌊(80 / 9 : ℝ)⌋ = 8 := by
        norm_num [Int.floor_eq_iff]
      rw [h1]
      norm_num
  · -- Now, prove that 80/9 is the greatest.
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : (⌊x⌋ : ℝ) / x = 9 / 10 := by
      simpa using hx2
    have h2 : (⌊x⌋ : ℝ) = 9 / 10 * x := by
      have : x ≠ 0 := hx1
      field_simp at h1 ⊢
      linarith
    let n := ⌊x⌋
    have hn1 : (n : ℝ) = 9 / 10 * x := by 
      simpa using h2
    have hn2 : (n : ℝ) ≤ x := by 
      exact Int.floor_le x
    have hn3 : x < (n + 1 : ℝ) := by 
      exact Int.lt_floor_add_one x
    have hn4 : (x : ℝ) < (10 : ℝ) := by
      nlinarith [hn1, hn3]
    have hn5 : (n : ℝ) < (9 : ℝ) := by
      nlinarith [hn1, hn4]
    have hn6 : n < 9 := by
      by_contra h
      push_neg at h
      have h7 : n ≥ 9 := by omega
      have hn7 : (n : ℝ) ≥ (9 : ℝ) := by 
        exact_mod_cast h7
      linarith
    have hn8 : n ≤ 8 := by 
      omega
    have hn9 : (n : ℝ) ≤ (8 : ℝ) := by 
      exact_mod_cast hn8
    nlinarith [hn1, hn9]