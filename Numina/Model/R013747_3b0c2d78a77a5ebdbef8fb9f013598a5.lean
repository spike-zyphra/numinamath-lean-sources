import Mathlib

theorem algebra_237508 (x : ℝ) : ⌊(9 * x - 4) / 6⌋ = (12 * x + 7) / 4 ↔
    x = -9 / 4 ∨ x = -23 / 12 := by
  constructor
  · -- Proof of the forward direction
    intro h
    let n := ⌊(9 * x - 4) / 6⌋
    have hn1 : (n : ℝ) = (12 * x + 7) / 4 := by
      exact_mod_cast h
    have h2 : (n : ℝ) ≤ (9 * x - 4) / 6 := by
      exact_mod_cast Int.floor_le ( (9 * x - 4) / 6 )
    have h3 : (9 * x - 4) / 6 < (n + 1 : ℝ) := by
      exact_mod_cast Int.lt_floor_add_one ( (9 * x - 4) / 6 )
    have hn2 : n ≤ 3 := by
      by_contra h6
      push_neg at h6
      have hn3 : n ≥ 4 := by omega
      have hn4 : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast hn3
      nlinarith
    have hn3 : n ≥ -6 := by
      by_contra h6
      push_neg at h6
      have hn4 : n ≤ -7 := by omega
      have hn5 : (n : ℝ) ≤ (-7 : ℝ) := by exact_mod_cast hn4
      nlinarith
    have h8 : n = -6 ∨ n = -5 ∨ n = -4 ∨ n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8)
    · -- n = -6
      have hn8 : (n : ℝ) = (-6 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      linarith
    · -- n = -5
      have hn8 : (n : ℝ) = (-5 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (-9 / 4 : ℝ) := by linarith
      left
      linarith
    · -- n = -4
      have hn8 : (n : ℝ) = (-4 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (-23 / 12 : ℝ) := by linarith
      right
      linarith
    · -- n = -3
      have hn8 : (n : ℝ) = (-3 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (-19 / 12 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = -2
      have hn8 : (n : ℝ) = (-2 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (-11 / 12 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = -1
      have hn8 : (n : ℝ) = (-1 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (-5 / 8 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = 0
      have hn8 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (7 / 48 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = 1
      have hn8 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (4 / 12 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = 2
      have hn8 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (1 / 4 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
    · -- n = 3
      have hn8 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast h8
      rw [hn8] at hn1
      have hx : x = (7 / 8 : ℝ) := by linarith
      rw [hx] at h2 h3
      norm_num at h2 h3
      all_goals
        try { exfalso <;> nlinarith }
  · -- Proof of the reverse direction
    rintro (h | h)
    · -- When x = -9/4
      rw [h]
      norm_num [Int.floor_eq_iff]
      all_goals norm_num
    · -- When x = -23/12
      rw [h]
      norm_num [Int.floor_eq_iff]
      all_goals norm_num