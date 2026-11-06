import Mathlib

theorem algebra_292908 {a b : ℝ} (h : a + ⌊a⌋ = b + ⌊b⌋) : a = b := by
  have h1 : (⌊a⌋ : ℝ) ≤ a := by exact Int.floor_le a
  have h2 : a < (⌊a⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one a
  have h3 : (⌊b⌋ : ℝ) ≤ b := by exact Int.floor_le b
  have h4 : b < (⌊b⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one b
  have h6 : ⌊a⌋ ≤ ⌊b⌋ := by
    by_contra h7
    push_neg at h7
    have h7' : ⌊a⌋ ≥ ⌊b⌋ + 1 := by omega
    have h8 : (⌊a⌋ : ℝ) ≥ (⌊b⌋ + 1 : ℝ) := by exact_mod_cast h7'
    nlinarith
  have h7 : ⌊b⌋ ≤ ⌊a⌋ := by
    by_contra h7
    push_neg at h7
    have h7' : ⌊b⌋ ≥ ⌊a⌋ + 1 := by omega
    have h8 : (⌊b⌋ : ℝ) ≥ (⌊a⌋ + 1 : ℝ) := by exact_mod_cast h7'
    nlinarith
  have h8 : ⌊a⌋ = ⌊b⌋ := by 
    omega
  have h9 : (⌊a⌋ : ℝ) = (⌊b⌋ : ℝ) := by exact_mod_cast h8
  linarith