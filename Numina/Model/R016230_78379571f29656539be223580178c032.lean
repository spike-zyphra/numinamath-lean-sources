import Mathlib

theorem algebra_199476 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 * (b + c - a) = b^2 * (c + a - b)) (h2 : b^2 * (c + a - b) = c^2 * (a + b - c)) :
    a = b ∧ b = c := by
  have h3 : (a - b) * (a * c + b * c - a^2 - b^2) = 0 := by
    nlinarith
  have h4 : (b - c) * (a * b + a * c - b^2 - c^2) = 0 := by
    nlinarith
  
  by_cases h : a - b = 0
  · -- Case where $a = b$
    have ha1 : a = b := by
      linarith
    have h41 : b - c = 0 ∨ (a * b + a * c - b^2 - c^2) = 0 := by
      cases (mul_eq_zero.mp h4) with
      | inl h31 => 
        left
        linarith
      | inr h32 =>
        right
        linarith
    cases h41 with
    | inl h5 =>
      have hb1 : b = c := by
        linarith
      constructor
      · linarith
      · linarith
    | inr h5 =>
      have eq1 : a = c := by
        have eq2 : a * b + a * c - b^2 - c^2 = 0 := by
          linarith
        have eq3 : a * a + a * c = a^2 + c^2 := by
          rw [show b = a by linarith] at eq2
          nlinarith
        have eq4 : a * c = c^2 := by
          nlinarith
        have eq5 : a = c := by
          apply (mul_left_inj' hc).mp
          linarith
        linarith
      constructor
      · linarith
      · linarith
  · -- Case where $a ≠ b$
    have h31 : a * c + b * c - a^2 - b^2 = 0 := by
      apply (mul_left_inj' (show (a - b) ≠ 0 by
        intro h'
        apply h
        linarith)).mp
      linarith

    by_cases h41 : b - c = 0
    · -- Case $b = c$
      have hb1 : b = c := by
        linarith
      have eq1 : a * c + b * c - a^2 - b^2 = 0 := h31
      rw [show c = b by linarith] at h31
      have eq2 : a * b = a^2 := by
        nlinarith
      have eq3 : b = a := by
        apply (mul_left_inj' ha).mp
        linarith
      have hne : a - b = 0 := by
        linarith
      contradiction
    · -- Case $b ≠ c$
      have h42 : a * b + a * c - b^2 - c^2 = 0 := by
        apply (mul_left_inj' (show (b - c) ≠ 0 by
          intro h'
          apply h41
          linarith)).mp
        linarith

      have h51 : (c - a) * (a + b + c) = 0 := by
        nlinarith

      cases (mul_eq_zero.mp h51) with
      | inl h52 =>
        have hca : c = a := by
          linarith
        rw [show c = a by linarith] at h31
        have eq1 : a * b = b^2 := by
          nlinarith
        have eq2 : a = b := by
          apply (mul_left_inj' hb).mp
          linarith
        have hne : a - b = 0 := by
          linarith
        contradiction
      | inr h52 =>
        have heq : a + b + c = 0 := by
          linarith
        have eq1 : c^2 + b^2 + b * c = 0 := by
          have h31' : a * c + b * c - a^2 - b^2 = 0 := h31
          have ha1 : a = -b - c := by linarith
          rw [ha1] at h31'
          nlinarith [sq_pos_of_ne_zero (show c ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_nonneg (b + c), sq_nonneg (b - c)]
        nlinarith [sq_pos_of_ne_zero (show c ≠ 0 by assumption), sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_nonneg (b + c), sq_nonneg (b - c)]