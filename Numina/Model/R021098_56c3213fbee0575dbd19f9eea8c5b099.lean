import Mathlib

theorem algebra_2131
    (a b c d : ℝ)
    (ha : 0 < a ∧ a ^ 2 = 2)
    (hb : 0 < b ∧ b ^ 3 = 3)
    (hc : 0 < c ∧ c ^ 4 = 4)
    (hd : 0 < d ∧ d ^ 5 = 5) :
    max (max a b) (max c d) = b := by
  rcases ha with ⟨ha_pos, ha2⟩
  rcases hb with ⟨hb_pos, hb3⟩
  rcases hc with ⟨hc_pos, hc4⟩
  rcases hd with ⟨hd_pos, hd5⟩
  have h1 : a < b := by
    have h1 : a ^ 6 < b ^ 6 := by
      calc
        a ^ 6 = (a ^ 2) ^ 3 := by ring
        _ = 2 ^ 3 := by rw [ha2]
        _ = 8 := by norm_num
        _ < 9 := by norm_num
        _ = 3 ^ 2 := by norm_num
        _ = (b ^ 3) ^ 2 := by rw [hb3]
        _ = b ^ 6 := by ring
    have h2 : a < b := by
      nlinarith [show a ^ 6 < b ^ 6 by linarith, sq_nonneg (a - b), sq_nonneg (a ^ 2 - 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg ((b: ℝ) ^ 2 - 2), sq_nonneg (b ^ 3 - 3)]
    linarith
  have h2 : c < b := by
    have h1 : c ^ 6 < b ^ 6 := by
      have hc6_eq : c ^ 6 = 8 := by
        have hc2' : c ^ 2 = 2 := by
          have h1 : c ^ 4 = 4 := hc4
          have h2 : (c ^ 2) ^ 2 = 4 := by
            nlinarith
          have h3 : c ^ 2 > 0 := by nlinarith [hc_pos]
          nlinarith
        calc
          c ^ 6 = (c ^ 4) * (c ^ 2) := by ring
          _ = 4 * (c ^ 2) := by rw [hc4]
          _ = 4 * 2 := by rw [hc2']
          _ = (8 : ℝ) := by norm_num
      have hb6_eq : b ^ 6 = 9 := by
        calc
          b ^ 6 = (b ^ 3) ^ 2 := by ring
          _ = 3 ^ 2 := by rw [hb3]
          _ = (9 : ℝ) := by norm_num
      rw [hc6_eq, hb6_eq]
      all_goals norm_num
    have h2 : c < b := by
      nlinarith [show c ^ 6 < b ^ 6 by linarith, sq_nonneg (c - b), sq_nonneg (c ^ 2 - 2), sq_nonneg (d ^ 2 - 2), sq_nonneg ((b: ℝ) ^ 2 - 2)]
    linarith
  have h3 : d < b := by
    have h3 : d ^ 15 < b ^ 15 := by
      calc
        d ^ 15 = (d ^ 5) ^ 3 := by ring
        _ = 5 ^ 3 := by rw [hd5]
        _ = 125 := by norm_num
        _ < 243 := by norm_num
        _ = 3 ^ 5 := by norm_num
        _ = (b ^ 3) ^ 5 := by rw [hb3]
        _ = b ^ 15 := by ring
    have h4 : d < b := by
      nlinarith [show d ^ 15 < b ^ 15 by linarith, sq_nonneg (d - b), sq_nonneg (d ^ 2 - 2), sq_nonneg (d ^ 2 - b ^ 2), sq_nonneg ((b: ℝ) ^ 2 - 2), sq_nonneg (b ^ 3 - 3)]
    linarith
  have h4 : max (max a b) (max c d) = b := by
    have h5 : max a b = b := by
      apply max_eq_right
      nlinarith
    have h6 : max c d ≤ b := by
      have hc10 : c ≤ b := by linarith
      have hc11 : d ≤ b := by linarith
      cases' max_cases c d with hcd hcd
      · linarith [hcd, hc10]
      · linarith [hcd, hc11]
    have h7 : max (max a b) (max c d) = b := by
      rw [h5]
      apply max_eq_left
      linarith
    exact h7
  exact h4