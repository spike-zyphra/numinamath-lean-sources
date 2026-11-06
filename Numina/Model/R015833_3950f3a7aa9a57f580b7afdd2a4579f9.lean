import Mathlib

theorem algebra_142271 (x : ℝ) (hx : ⌊x⌋ * (x - ⌊x⌋) + x = 2 * (x - ⌊x⌋) + 6) :
    x = 14 / 3 ∨ x = 21 / 4 ∨ x = 6 := by
  have h1 : ⌊x⌋ ≤ (x : ℝ) := by
    exact Int.floor_le x
  have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h3 : ⌊x⌋ ≥ 0 := by
    by_contra h
    push_neg at h
    have h4 : ⌊x⌋ ≤ -1 := by
      omega
    have h5 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by
      exact_mod_cast h4
    nlinarith
  have h4 : ⌊x⌋ ≤ 10 := by
    by_contra h
    push_neg at h
    have h10 : ⌊x⌋ ≥ 11 := by
      omega
    have h11 : (⌊x⌋ : ℝ) ≥ 11 := by
      exact_mod_cast h10
    nlinarith
  have h5 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 ∨ ⌊x⌋ = 4 ∨ ⌊x⌋ = 5 ∨ ⌊x⌋ = 6 ∨ ⌊x⌋ = 7 ∨ ⌊x⌋ = 8 ∨ ⌊x⌋ = 9 ∨ ⌊x⌋ = 10 := by
    omega
  rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5)
  · -- case ⌊x⌋ = 0
    have h14 : ⌊x⌋ = 0 := by 
      omega
    have hx0 : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (0 : ℝ) by linarith [hx0] ] at hx
    exfalso
    nlinarith
  · -- case ⌊x⌋ = 1 
    have h14 : ⌊x⌋ = 1 := by
      omega
    have hx1 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (1 : ℝ) by linarith [hx1] ] at hx
    exfalso 
    nlinarith
  · -- case ⌊x⌋ = 2 
    have h14 : ⌊x⌋ = 2 := by 
      omega
    have hx2 : (⌊x⌋ : ℝ) = (2 : ℝ) := by
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (2 : ℝ) by linarith [hx2] ] at hx
    have h4 : x = (6 : ℝ) := by 
      nlinarith
    have h7 : x < (3 : ℝ) := by 
      have h8 : ⌊x⌋ = 2 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith
  · -- case ⌊x⌋ = 3 
    have h14 : ⌊x⌋ = 3 := by
      omega
    have hx3 : (⌊x⌋ : ℝ) = (3 : ℝ) := by
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (3 : ℝ) by linarith [hx3] ] at hx
    have h4 : x = 9 / 2 := by 
      nlinarith
    have h7 : x < (4 : ℝ) := by
      have h8 : ⌊x⌋ = 3 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith
  · -- case ⌊x⌋ = 4 
    have h14 : ⌊x⌋ = 4 := by 
      omega
    have hx4 : (⌊x⌋ : ℝ) = (4 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (4 : ℝ) by linarith [hx4] ] at hx
    have h4 : x = (14 / 3 : ℝ) := by 
      nlinarith
    left
    exact_mod_cast h4
  · -- case ⌊x⌋ = 5 
    have h14 : ⌊x⌋ = 5 := by 
      omega
    have hx5 : (⌊x⌋ : ℝ) = (5 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (5 : ℝ) by linarith [hx5] ] at hx
    have h4 : x = (21 / 4 : ℝ) := by 
      nlinarith
    right
    left 
    exact_mod_cast h4
  · -- case ⌊x⌋ = 6 
    have h14 : ⌊x⌋ = 6 := by 
      omega
    have hx6 : (⌊x⌋ : ℝ) = (6 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (6 : ℝ) by linarith [hx6] ] at hx
    have h4 : x = (6 : ℝ) := by 
      nlinarith
    right
    right 
    exact_mod_cast h4
  · -- case ⌊x⌋ = 7 
    have h14 : ⌊x⌋ = 7 := by 
      omega
    have hx7 : (⌊x⌋ : ℝ) = (7 : ℝ) := by
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (7 : ℝ) by linarith [hx7] ] at hx
    have h4 : x = (41 / 6 : ℝ) := by 
      nlinarith
    have h7 : x < (8 : ℝ) := by 
      have h8 : ⌊x⌋ = 7 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith
  · -- case ⌊x⌋ = 8 
    have h14 : ⌊x⌋ = 8 := by 
      omega
    have hx8 : (⌊x⌋ : ℝ) = (8 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (8 : ℝ) by linarith [hx8] ] at hx
    have h4 : x = (54 / 7 : ℝ) := by 
      nlinarith
    have h7 : x < (9 : ℝ) := by
      have h8 : ⌊x⌋ = 8 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith
  · -- case ⌊x⌋ = 9 
    have h14 : ⌊x⌋ = 9 := by 
      omega
    have hx9 : (⌊x⌋ : ℝ) = (9 : ℝ) := by 
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (9 : ℝ) by linarith [hx9] ] at hx
    have h4 : x = (69 / 8 : ℝ) := by 
      nlinarith
    have h7 : x < (10 : ℝ) := by 
      have h8 : ⌊x⌋ = 9 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith
  · -- case ⌊x⌋ = 10 
    have h14 : ⌊x⌋ = 10 := by 
      omega
    have hx10 : (⌊x⌋ : ℝ) = (10 : ℝ) := by
      exact_mod_cast h14
    rw [show (⌊x⌋ : ℝ) = (10 : ℝ) by linarith [hx10] ] at hx
    have h4 : x = (86 / 9 : ℝ) := by 
      nlinarith
    have h7 : x < (11 : ℝ) := by
      have h8 : ⌊x⌋ = 10 := h14
      have h9 : (x : ℝ) < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have h10 : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    linarith