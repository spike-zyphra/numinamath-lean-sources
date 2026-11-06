import Mathlib

theorem algebra_5780 :
    IsGreatest {c * a * t * s + g * o | (c : ℕ) (a : ℕ) (t : ℕ) (s : ℕ) (g : ℕ) (o : ℕ) (hc : c > 0) (ha : a > 0) (ht : t > 0) (hs : s > 0) (hg : g > 0) (ho : o > 0) (h1 : c * a * t = 5) (h2 : s * a * t = 75) (h3 : c * s * g * o = 45)} 78 := by
  constructor
  · -- Show 78 is in the set.
    use 1, 1, 5, 15, 1, 3
    all_goals norm_num
  · -- Show 78 is the greatest.
    intro x hx
    rcases hx with ⟨c, a, t, s, g, o, hc, ha, ht, hs, hg, ho, h1, h2, h3, hx⟩
    have h4 : c ∣ 5 := by 
      use a * t
      all_goals linarith [h1]
    have h5 : c = 1 ∨ c = 5 := by 
      have h6 : c ∣ 5 := h4
      have h7 : c ≤ 5 := by 
        exact Nat.le_of_dvd (show 0 < 5 by norm_num) h6
      interval_cases c <;> tauto
    rcases h5 with (h6 | h6)
    · -- Case c = 1
      have hc1 : c = 1 := h6
      -- From h1: 1 * a * t = 5 => a * t = 5
      have h8 : a * t = 5 := by 
        rw [hc1] at h1 
        nlinarith
      -- From h2: s * a * t = 75 => s * 5 = 75 => s = 15
      have h7 : s = 15 := by 
        have h18 : a * t = 5 := h8 
        have : s * 5 = 75 := by 
          calc 
            s * 5 = s * (a * t) := by 
              rw [h18] 
            _ = 75 := by 
              linarith [h2]
        omega 
      -- From h3: c * s * g * o = 45 => 1 * 15 * g * o = 45 => 15 * g * o = 45 => g * o = 3
      have h9 : g * o = 3 := by 
        rw [hc1, h7] at h3 
        nlinarith 
      -- Compute the expression value 
      have h10 : c * a * t * s = 75 := by 
        calc 
          c * a * t * s = 1 * (a * t) * s := by 
            rw [hc1] 
            <;> ring 
          _ = 1 * 5 * s := by 
            rw [h8] 
            <;> ring 
          _ = 1 * 5 * 15 := by 
            rw [h7] 
          _ = 75 := by 
            norm_num 
      -- The value of total expression 
      nlinarith [h10, h9, hx] 
    · -- Case c = 5
      have hc1 : c = 5 := h6 
      -- From h1: 5 * a * t = 5 => a * t = 1 
      have h13 : a * t = 1 := by 
        rw [hc1] at h1 
        nlinarith 
      -- From h2: s * a * t = 75 => s * 1 = 75 => s = 75 
      have h14 : s = 75 := by 
        have h18 : a * t = 1 := h13 
        have : s * 1 = 75 := by 
          calc 
            s * 1 = s * (a * t) := by 
              rw [h18] 
            _ = 75 := by 
              linarith [h2]
        omega 
      -- From h3: c * s * g * o = 45 => 5 * 75 * g * o = 45 => 375 * g * o = 45 => Contradiction 
      rw [hc1, h14] at h3
      nlinarith