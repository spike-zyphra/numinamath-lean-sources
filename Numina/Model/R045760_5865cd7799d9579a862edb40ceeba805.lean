import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189093 :
  IsLeast {x | ∃ a b : ℝ, x = max (max (a^2 + abs b) ((a + 2)^2 + abs b)) (a^2 + abs (b - 1))} 1.5 := by
  constructor
  · -- Show 1.5 is in the set 
    use -1, 0.5 
    norm_num [abs_of_nonneg, abs_of_nonpos, abs, max_assoc, max_comm, max_left_comm]
  · -- Show that 1.5 is the smallest in the set
    intro x hx 
    rcases hx with ⟨a, b, hx⟩ 
    by_contra h 
    push_neg at h 
    rw [hx] at h 
    have h1 : max (max (a ^ 2 + abs b) ((a + 2) ^ 2 + abs b)) (a ^ 2 + abs (b - 1)) < 1.5 := by linarith
    have h2 : a ^ 2 + abs b < 1.5 := by
      have h3 : max (max (a ^ 2 + abs b) ((a + 2) ^ 2 + abs b)) (a ^ 2 + abs (b - 1)) ≥ a ^ 2 + abs b := by 
        simp [max_le_iff]
      linarith 
    have h3 : (a + 2) ^ 2 + abs b < 1.5 := by 
      have h4 : max (max (a ^ 2 + abs b) ((a + 2) ^ 2 + abs b)) (a ^ 2 + abs (b - 1)) ≥ (a + 2) ^ 2 + abs b := by 
        simp [max_le_iff]
      linarith 
    have h4 : a ^ 2 + abs (b - 1) < 1.5 := by
      have h5 : max (max (a ^ 2 + abs b) ((a + 2) ^ 2 + abs b)) (a ^ 2 + abs (b - 1)) ≥ a ^ 2 + abs (b - 1) := by 
        simp [max_le_iff]
      linarith 
    by_cases h5 : b ≥ 0 
    · -- case b ≥ 0, so abs b = b, abs (b - 1) = abs (b - 1)
      have hb1 : abs b = b := abs_of_nonneg h5 
      by_cases h6 : b ≥ 1 
      · -- case b ≥ 1, so abs (b - 1) = b - 1 
        have hb2 : abs (b - 1) = b - 1 := by
          rw [abs_of_nonneg]
          linarith 
        rw [hb1] at h2 h3 
        rw [hb2] at h4 
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 0.5)]
      · -- case 0 ≤ b < 1, so abs (b - 1) = 1 - b 
        have hb2 : abs (b - 1) = 1 - b := by 
          rw [abs_of_neg]
          linarith 
          all_goals linarith 
        rw [hb1] at h2 h3 
        rw [hb2] at h4 
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 0.5)]
    · -- case b < 0, so abs b = -b, abs (b - 1) = 1 - b 
      have hb1 : abs b = -b := by 
        rw [abs_of_neg]
        linarith 
        all_goals linarith 
      have hb2 : abs (b - 1) = 1 - b := by
        rw [abs_of_neg]
        linarith 
        all_goals linarith 
      rw [hb1] at h2 h3 
      rw [hb2] at h4 
      nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 0.5), sq_nonneg (b - 0.5)]