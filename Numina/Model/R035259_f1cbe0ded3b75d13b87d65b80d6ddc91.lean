import Mathlib

theorem algebra_116193 {a b : ℕ → ℝ} {q : ℝ} (hq : q ≠ 1)
    (ha : ∀ n, a n = a 0 * q ^ n) (hb1 : b 1 = a 0 + a 1 + a 2)
    (hb2 : b 2 = a 3 + a 4 + a 5) (hb3 : b 3 = a 6 + a 7 + a 8)
    (hb : ∀ n, b n = a (3 * n - 2) + a (3 * n - 1) + a (3 * n)) :
    ∃ r, ∀ n, b (n + 1) = r * b n := by
  have eq1 := hb 1
  have eq1' : b 1 = a 1 + a 2 + a 3 := by
    simpa using eq1
  have h1 := hb1
  have h2 : a 1 = a 0 * q ^ 1 := by 
    specialize ha 1
    simpa using ha
  have h3 : a 2 = a 0 * q ^ 2 := by 
    specialize ha 2
    simpa using ha
  have h4 : a 3 = a 0 * q ^ 3 := by 
    specialize ha 3
    simpa using ha
  rw [h2, h3, h4] at eq1'
  have eq3 : a 0 * (1 - q ^ 3) = 0 := by 
    linarith [ h1, eq1' ]
  have h5 : a 0 = 0 := by 
    have h6 : 1 - q ^ 3 ≠ 0 := by 
      by_contra h 
      have hq1 : q ^ 3 = 1 := by linarith 
      have h7 : q ^ 3 - 1 = 0 := by 
        linarith 
      have h8 : (q - 1) * (q ^ 2 + q + 1) = 0 := by 
        ring_nf at h7 ⊢ 
        linarith 
      cases' (mul_eq_zero.1 h8) with h9 h10 
      · -- Case q - 1 = 0, so q = 1 
        exfalso 
        apply hq 
        linarith 
      · -- Case q ^ 2 + q + 1 = 0 
        have h11 : q ^ 2 + q + 1 > 0 := by 
          nlinarith [sq_pos_of_ne_zero (show (q - 1 : ℝ) ≠ 0 by 
            intro h' 
            apply hq 
            linarith 
          ), sq_nonneg (q + 1 / 2)]
        nlinarith 
    have h7 : a 0 * (1 - q ^ 3) = 0 := eq3 
    have h9 : a 0 = 0 := by 
      apply (mul_left_inj' h6).mp 
      linarith 
    exact h9 
  have h7 : ∀ (n : ℕ), a n = 0 := by 
    intro n 
    rw [ha n, h5] 
    all_goals norm_num 
  use 0 
  intro n 
  have h8 : ∀ (n : ℕ), b n = 0 := by 
    intro n 
    induction n with 
    | zero => 
      have eq1 := hb 0 
      norm_num [h7 0, h7 1, h7 2, h7 3, h7 4, h7 5, h7 6, h7 7, h7 8] at eq1 ⊢
      all_goals linarith 
    | succ n ih => 
      have eq1 := hb (n + 1) 
      norm_num [h7, ih] at eq1 ⊢
      all_goals linarith 
  simp [h8 (n + 1), h8 n]