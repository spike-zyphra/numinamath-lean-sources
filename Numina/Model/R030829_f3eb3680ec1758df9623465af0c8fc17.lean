import Mathlib

theorem number_theory_27112 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (habc : a + b + c ≠ 0) (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) (n : ℕ) (hn : Odd n) :
    1 / a ^ n + 1 / b ^ n + 1 / c ^ n = 1 / (a ^ n + b ^ n + c ^ n) := by

  have h1 : (a + b) * (b + c) * (c + a) = 0 := by
    field_simp [ha, hb, hc, habc] at h
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero habc]

  have h2 : (a + b) = 0 ∨ (b + c) = 0 ∨ (c + a) = 0 := by
    cases (mul_eq_zero.mp h1) with
    | inl h11 =>
      cases (mul_eq_zero.mp h11) with
      | inl h22 => 
        left
        linarith
      | inr h33 => 
        right
        left
        linarith
    | inr h44 => 
      right
      right
      linarith

  rcases h2 with (h2 | h2 | h2)
  · -- case a + b = 0
    have ha1 : a = -b := by linarith
    have ha2 : a ^ n = - b ^ n := by
      rw [ha1]
      have h2 : (-b : ℝ) ^ n = - (b ^ n) := by
        have h3 : Odd n := hn
        have h4 : (-b : ℝ) ^ n = - (b ^ n) := by
          apply Odd.neg_pow
          exact h3
        linarith
      linarith
    have h3 : a ^ n + b ^ n + c ^ n = c ^ n := by
      linarith [ha2]
    have h4 : 1 / a ^ n + 1 / b ^ n + 1 / c ^ n = 1 / c ^ n := by
      have h5 : 1 / a ^ n = 1 / (-b ^ n) := by
        rw [show a ^ n = - b ^ n by linarith [ha2]]
      rw [h5]
      have h7 : 1 / (-b ^ n) + 1 / b ^ n = 0 := by
        have h8 : 1 / (-b ^ n) = - (1 / b ^ n) := by
          field_simp [hb]
        rw [h8]
        all_goals ring
      have h9 : 1 / (-b ^ n) + 1 / b ^ n + 1 / c ^ n = 1 / c ^ n := by
        have h77 : 1 / (-b ^ n) + 1 / b ^ n = 0 := h7
        linarith
      linarith
    rw [h4, h3]
  · -- case b + c = 0
    have hb1 : b = -c := by linarith
    have hb2 : b ^ n = - c ^ n := by
      rw [hb1]
      have h2 : (-c : ℝ) ^ n = - (c ^ n) := by
        have h3 : Odd n := hn
        have h4 : (-c : ℝ) ^ n = - (c ^ n) := by
          apply Odd.neg_pow
          exact h3
        linarith
      linarith
    have h3 : a ^ n + b ^ n + c ^ n = a ^ n := by
      linarith [hb2]
    have h4 : 1 / a ^ n + 1 / b ^ n + 1 / c ^ n = 1 / a ^ n := by
      have h5 : 1 / b ^ n = 1 / (-c ^ n) := by
        rw [hb2]
      rw [h5]
      have h7 : 1 / (-c ^ n) + 1 / c ^ n = 0 := by
        have h8 : 1 / (-c ^ n) = - (1 / c ^ n) := by
          field_simp [hc]
        rw [h8]
        all_goals ring
      have h9 : 1 / a ^ n + (1 / (-c ^ n) + 1 / c ^ n) = 1 / a ^ n := by
        have h77 : 1 / (-c ^ n) + 1 / c ^ n = 0 := h7
        linarith
      linarith
    rw [h4, h3]
  · -- case c + a = 0
    have hc1 : c = -a := by linarith
    have hc2 : c ^ n = - a ^ n := by
      rw [hc1]
      have h2 : (-a : ℝ) ^ n = - (a ^ n) := by
        have h3 : Odd n := hn
        have h4 : (-a : ℝ) ^ n = - (a ^ n) := by
          apply Odd.neg_pow
          exact h3
        linarith
      linarith
    have h3 : a ^ n + b ^ n + c ^ n = b ^ n := by
      linarith [hc2]
    have h4 : 1 / a ^ n + 1 / b ^ n + 1 / c ^ n = 1 / b ^ n := by
      have h5 : 1 / c ^ n = 1 / (-a ^ n) := by
        rw [hc2]
      rw [h5]
      have h7 : 1 / a ^ n + 1 / (-a ^ n) = 0 := by
        have h8 : 1 / (-a ^ n) = - (1 / a ^ n) := by
          field_simp [ha]
        rw [h8]
        all_goals ring
      have h9 : (1 / a ^ n + 1 / (-a ^ n)) + 1 / b ^ n = 1 / b ^ n := by
        have h77 : 1 / a ^ n + 1 / (-a ^ n) = 0 := h7
        linarith
      linarith
    rw [h4, h3]