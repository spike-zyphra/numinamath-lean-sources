import Mathlib

theorem number_theory_4835_1 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a > 0 ∧ b > 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  
  have le_a := Int.floor_le a
  
  have le_b := Int.floor_le b
  
  have := mul_le_mul le_a le_b (by simp [Int.floor_nonneg]; linarith) (by linarith)
  
  rw [←Int.cast_mul, ←Int.le_floor] at this
  apply this

theorem number_theory_4835_2 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a < 0 ∧ b < 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  
  have h1 := Int.floor_le a
  
  have h2 := Int.floor_le b
  
  have h3 : a < (0 : ℝ) := by linarith
  
  have h4 : b < (0 : ℝ) := by linarith
  
  have h5 : a * b > (0 : ℝ) := mul_pos_of_neg_of_neg h3 h4
  
  have h6 : (⌊a⌋ : ℝ) ≤ a := by exact Int.floor_le a
  
  have h7 : (⌊b⌋ : ℝ) ≤ b := by exact Int.floor_le b
  
  have h8 : (⌊a⌋ : ℝ) < (0 : ℝ) := by
    by_contra h
    push_neg at h
    have : a ≥ (0 : ℝ) := by linarith
    linarith
  
  have h9 : (⌊b⌋ : ℝ) < (0 : ℝ) := by
    by_contra h
    push_neg at h
    have : b ≥ (0 : ℝ) := by linarith
    linarith
  
  have h10 : (⌊a⌋ * ⌊b⌋ : ℝ) ≥ a * b := by
    nlinarith
  
  have h11 : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
    by_contra h
    push_neg at h
    have h2 : ⌊a * b⌋ < ⌊a⌋ * ⌊b⌋ := by linarith
    have h3 : ⌊a * b⌋ < ⌊a⌋ * ⌊b⌋ := by linarith
    have h6 : (⌊a * b⌋ : ℝ) < (⌊a⌋ * ⌊b⌋ : ℝ) := by exact_mod_cast h2
    have h8 : (⌊a * b⌋ : ℝ) ≥ a * b - 1 := by
      have h14 : (⌊a * b⌋ + 1 : ℝ) > a * b := Int.lt_floor_add_one (a * b)
      linarith
    nlinarith [Int.floor_le (a * b), Int.floor_le (a), Int.floor_le (b), Int.lt_floor_add_one (a * b)]
  exact_mod_cast h11