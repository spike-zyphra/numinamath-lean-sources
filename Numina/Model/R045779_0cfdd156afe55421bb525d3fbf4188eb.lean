import Mathlib

theorem algebra_101554 {a b c x1 x2 : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hroots : {x | a * x ^ 2 + b * x + c = 0} = {x1, x2}) (hx1 : x1 = 4 * x2) :
    b ^ 2 / (a * c) = 25 / 4 := by
  have h1 : x1 ∈ {x | a * x ^ 2 + b * x + c = 0} := by
    rw [hroots]
    simp
  have h2 : x2 ∈ {x | a * x ^ 2 + b * x + c = 0} := by
    rw [hroots]
    simp
  have eq1 : a * x1 ^ 2 + b * x1 + c = 0 := by
    simpa using h1
  have eq2 : a * x2 ^ 2 + b * x2 + c = 0 := by
    simpa using h2
  rw [hx1] at eq1
  have eq3 : a * (4 * x2) ^ 2 + b * (4 * x2) + c = 0 := by
    linarith
  have eq4 : a * x2 ^ 2 + b * x2 + c = 0 := eq2
  have eq5 : 15 * a * x2 ^ 2 + 3 * b * x2 = 0 := by
    nlinarith
  have eq7 : (5 * a * x2 + b) * x2 = 0 := by
    linarith
  cases' (mul_eq_zero.mp eq7) with h7 h8
  · -- Case 1: 5 * a * x2 + b = 0
    have hb : b = -5 * a * x2 := by
      linarith
    have hc1 : c = 4 * a * x2 ^ 2 := by
      rw [hb] at eq4
      nlinarith
    have ha1 : a * x2 ≠ 0 := by
      by_contra h
      have hx2_0 : x2 = 0 := by
        have h3 : a * x2 = 0 := by linarith [h]
        have h4 : a ≠ 0 := ha
        have : x2 = 0 := by
          apply (mul_left_inj' h4).mp
          linarith
        assumption
      rw [hx2_0] at hc1
      have hc0 : c = 0 := by
        nlinarith
      contradiction
    have h8 : b ^ 2 / (a * c) = 25 / 4 := by
      rw [hb, hc1]
      have ha1' : a * x2 ≠ 0 := by
        by_contra h
        have hx2_0 : x2 = 0 := by
          have h3 : a * x2 = 0 := by linarith [h]
          have h4 : a ≠ 0 := ha
          have : x2 = 0 := by
            apply (mul_left_inj' h4).mp
            linarith
          assumption
        rw [hx2_0] at hc1
        have hc0 : c = 0 := by
          nlinarith
        contradiction
      have h9 : ((-5 * a * x2) ^ 2) / (a * (4 * a * x2 ^ 2)) = (25 * a ^ 2 * x2 ^ 2) / (a * (4 * a * x2 ^ 2)) := by
        ring
      have h10 : (25 * a ^ 2 * x2 ^ 2) / (a * (4 * a * x2 ^ 2)) = 25 / 4 := by
        have hx2 : x2 ≠ 0 := by
          by_contra h
          have hx2_0 : x2 = 0 := by linarith [h]
          rw [hx2_0] at hc1
          have hc0 : c = 0 := by
            nlinarith
          contradiction
        have h5 : a * (4 * a * x2 ^ 2) ≠ 0 := by
          have hx2 : x2 ≠ 0 := by
            by_contra h
            have hx2_0 : x2 = 0 := by linarith [h]
            rw [hx2_0] at hc1
            have hc0 : c = 0 := by
              nlinarith
            contradiction
          have h5 : a * (4 * a * x2 ^ 2) ≠ 0 := by
            have h6 : 4 * a * x2 ^ 2 ≠ 0 := by
              have h7 : a ≠ 0 := ha
              have h8 : x2 ≠ 0 := hx2
              have h9 : x2 ^ 2 ≠ 0 := by
                apply pow_ne_zero 2
                exact h8
              have : a * x2 ^ 2 ≠ 0 := by
                exact mul_ne_zero h7 h9
              have h5 : 4 * (a * x2 ^ 2) ≠ 0 := by
                simp [show (4 : ℝ) ≠ 0 by norm_num, this]
              simpa using h5
            simp [show a ≠ 0 by exact ha, h6]
          assumption
        field_simp [show a * x2 ≠ 0 by exact ha1', h5]
        <;> nlinarith [sq_pos_of_pos (show 0 < 2 by norm_num), sq_nonneg (a * x2), sq_nonneg (x2), sq_nonneg (a), sq_nonneg (4 * x2), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hx2]
      rw [h9]
      exact h10
    exact h8
  · -- Case 2: x2 = 0
    have hx20 : x2 = 0 := by
      linarith
    have hc0 : c = 0 := by
      rw [hx20] at eq4
      nlinarith
    contradiction