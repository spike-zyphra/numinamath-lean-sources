import Mathlib

open Real

theorem algebra_184937 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hne1a : a ≠ 1) (hne1b : b ≠ 1) (x : ℝ) (hx : 0 < x) :
    (logb a x) * (logb b x) = logb a b ↔ x = b ∨ x = 1 / b := by 
  constructor
  · -- Assume $(\logb a x) * (\logb b x) = \logb a b$ and prove $x = b \vee x = 1/b$
    intro h_eq
    have h1 : logb a x = log x / log a := by
      field_simp [logb]
    have h2 : logb b x = log x / log b := by
      field_simp [logb]
    have h3 : logb a b = log b / log a := by
      field_simp [logb]
      all_goals linarith
    rw [h1, h2, h3] at h_eq
    have h4 : log a ≠ 0 := by
      have h5 : a > 0 := by linarith
      have h6 : a ≠ 1 := hne1a
      exact log_ne_zero_of_pos_of_ne_one h5 h6
    have h7 : log b ≠ 0 := by
      have h8 : b > 0 := by linarith
      have h9 : b ≠ 1 := hne1b
      exact log_ne_zero_of_pos_of_ne_one h8 h9
    have h_eq2 : (log x) ^ 2 = (log b) ^ 2 := by
      have h6 : log a ≠ 0 := h4
      have h7 : log b ≠ 0 := h7
      have h_eq3 : (log x) ^ 2 * log a = (log b) ^ 2 * log a := by
        field_simp [h6, h7] at h_eq
        linarith 
      have h6 : log a ≠ 0 := h4
      apply (mul_left_inj' h6).mp
      linarith 
    have h8 : log x = log b ∨ log x = - log b := by
      have h9 : (log x - log b) * (log x + log b) = 0 := by
        nlinarith 
      cases (mul_eq_zero.mp h9) with
      | inl h10 => 
        left
        linarith 
      | inr h11 => 
        right
        linarith 
    cases h8 with
    | inl h9 =>
      have h10 : x = b := by
        have h11 : log x = log b := by linarith 
        have h12 : x > 0 := by linarith 
        have h13 : b > 0 := by linarith 
        exact log_injOn_pos (Set.mem_Ioi.mpr h12) (Set.mem_Ioi.mpr h13) h11
      left
      exact h10
    | inr h9 =>
      have h14 : x = 1 / b := by
        have h15 : log x = - log b := by linarith 
        have h16 : log x = log (1 / b) := by
          have h17 : log (1 / b) = - log b := by
            simp [log_div, log_one]
          linarith 
        have h17 : x > 0 := by linarith 
        have h18 : (1 / b) > 0 := by
          positivity 
        exact log_injOn_pos (Set.mem_Ioi.mpr h17) (Set.mem_Ioi.mpr h18) h16
      right
      exact h14
  · -- Assume x = b ∨ x = 1 / b, prove (logb a x) * (logb b x) = logb a b
    rintro (h_eq | h_eq)
    · -- Case x = b
      rw [h_eq]
      have h5 : logb a b = log b / log a := by
        field_simp [logb]
      have h6 : logb b b = 1 := by
        -- Use change of base formula and simplify
        have h7 : logb b b = log b / log b := by
          simp [logb]
        have h8 : log b ≠ 0 := by
          have h9 : b > 0 := by linarith 
          have h10 : b ≠ 1 := hne1b
          exact log_ne_zero_of_pos_of_ne_one h9 h10 
        rw [h7]
        field_simp [h8]
        all_goals linarith 
      simp [show log a ≠ 0 by exact log_ne_zero_of_pos_of_ne_one ha hne1a, h5, h6]
      <;> field_simp <;> linarith 
      all_goals linarith 
    · -- Case x = 1 / b
      rw [h_eq]
      simp [show log a ≠ 0 by exact log_ne_zero_of_pos_of_ne_one ha hne1a, show log b ≠ 0 by exact log_ne_zero_of_pos_of_ne_one hb hne1b, logb, log_div, log_one]
      <;> ring_nf <;> field_simp <;> linarith 
      all_goals linarith