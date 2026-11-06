import Mathlib

theorem algebra_13077 {x : ℝ} (hx : Int.fract x = 0) :
    Int.ceil x - x = 0 := by 
  have h1 : Int.fract x = x - (⌊x⌋ : ℝ) := by 
    rw [Int.fract]
    <;> ring_nf <;> norm_num
  have h2 : x - (⌊x⌋ : ℝ) = 0 := by
    rw [h1] at hx
    linarith
  have h3 : x = (⌊x⌋ : ℝ) := by 
    linarith
  have h4 : Int.ceil x = ⌊x⌋ := by 
    rw [Int.ceil_eq_iff]
    constructor
    · -- Show that ↑⌊x⌋ ≤ x 
      have h5 : (⌊x⌋ : ℝ) ≤ x := by 
        have h6 : x = (⌊x⌋ : ℝ) := h3 
        linarith 
      linarith 
    · -- Show that x < ↑⌊x⌋ + 1 
      have h7 : x < (⌊x⌋ : ℝ) + 1 := by 
        have h8 : x = (⌊x⌋ : ℝ) := h3 
        linarith 
      linarith 
  rw [h4]
  rw [h3]
  all_goals norm_num
  all_goals linarith