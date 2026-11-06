import Mathlib

theorem algebra_207832 :
    IsGreatest {a : ℤ | ∃ x : ℤ, x^2 - (a + 7)*x + 7*a = -3} 11 := by
  constructor
  · -- Show 11 is in the set
    use 10
    norm_num
  · -- Show that for any a in the set, a ≤ 11
    intro a ha
    rcases ha with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have eq1 : x^2 - (a + 7) * x + 7 * a = -3 := by 
      linarith [hx]
    -- Rewrite equation to (x - 7) * (a - x) = 3
    have h1 : (x - 7) * (a - x) = 3 := by
      nlinarith
    -- From h1, x -7 divides 3.
    have h2 : (x - 7) ∣ 3 := by 
      use (a - x)
      all_goals linarith
    -- Since x -7 divides 3, it must be in [-3, -1, 1, 3]
    have h7 : (x - 7) = 1 ∨ (x - 7) = 3 ∨ (x - 7) = -1 ∨ (x - 7) = -3 := by
      have h8 : (x - 7) ∣ 3 := h2
      have h9 : (x - 7) ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : (x - 7) ≥ -3 := by
        have h7 : (- (x - 7)) ∣ 3 := by
          exact Int.neg_dvd.2 h8
        have h8 : - (x - 7) ≤ 3 := by 
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases h : x - 7 <;> tauto
    rcases h7 with (h7 | h7 | h7 | h7)
    · -- x - 7 = 1
      have hx8 : x = 8 := by
        omega
      rw [hx8] at h1
      omega
    · -- x - 7 = 3
      have hx10 : x = 10 := by
        omega
      rw [hx10] at h1
      omega
    · -- x - 7 = -1
      have hx6 : x = 6 := by
        omega
      rw [hx6] at h1
      omega
    · -- x - 7 = -3
      have hx4 : x = 4 := by
        omega
      rw [hx4] at h1
      omega