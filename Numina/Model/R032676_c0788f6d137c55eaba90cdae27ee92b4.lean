import Mathlib
theorem algebra_607356 {a b : ℝ} (ha : a + ⌊a⌋ = b + ⌊b⌋) : a = b := by 
  have h1 : (⌊a⌋ : ℝ) ≤ a := by exact Int.floor_le a
  have h2 : a < (⌊a⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one a
  have h3 : (⌊b⌋ : ℝ) ≤ b := by exact Int.floor_le b
  have h4 : b < (⌊b⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one b
  have h9 : ⌊a⌋ ≤ ⌊b⌋ := by 
    by_contra h
    push_neg at h 
    have h10 : ⌊a⌋ > ⌊b⌋ := by omega
    have h11 : (⌊a⌋ : ℝ) ≥ (⌊b⌋ + 1 : ℝ) := by exact_mod_cast h10
    nlinarith [ha, h1, h2, h3, h4, h11]
  have h10 : ⌊b⌋ ≤ ⌊a⌋ := by 
    by_contra h 
    push_neg at h 
    have  h11 : ⌊b⌋ > ⌊a⌋ := by omega
    have h12 : (⌊b⌋ : ℝ) ≥ (⌊a⌋ + 1 : ℝ) := by exact_mod_cast  h11
    nlinarith [ha, h1, h2, h3, h4, h12]
  have h11 : ⌊a⌋ = ⌊b⌋ := by 
    linarith
  have h12 : (⌊a⌋ : ℝ) = (⌊b⌋ : ℝ) := by 
    exact_mod_cast h11 
  linarith [ha, h12]