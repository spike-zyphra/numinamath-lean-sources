import Mathlib

theorem algebra_77022 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : abs a ≠ abs b)
  (h1 : (a + b) / (a - b) + (a - b) / (a + b) = 6) :
  (a ^ 3 + b ^ 3) / (a ^ 3 - b ^ 3) + (a ^ 3 - b ^ 3) / (a ^ 3 + b ^ 3) = 18 / 7 := by

  have h2 : a - b ≠ 0 := by
    by_contra h2
    have h3 : a = b := by linarith
    have h4 : abs a = abs b := by
      rw [show b = a by linarith [h3]]
    tauto

  have h3 : a + b ≠ 0 := by
    by_contra h3
    have h4 : a = -b := by linarith
    have h5 : abs a = abs b := by
      rw [show a = -b by linarith [h4]]
      rw [abs_neg]
    tauto

  have eq1 : (a + b) ^ 2 + (a - b) ^ 2 = 6 * ((a - b) * (a + b)) := by
    have eq2 : (a + b) / (a - b) + (a - b) / (a + b) = 6 := h1
    field_simp [h2, h3] at eq2 ⊢
    nlinarith

  have eq2 : a ^ 2 = 2 * b ^ 2 := by
    nlinarith

  have h4 : a ^ 3 - b ^ 3 ≠ 0 := by
    by_contra h4
    have eq4 : a ^ 3 = b ^ 3 := by linarith
    have eq5 : a ^ 2 + a * b + b ^ 2 = 0 := by
      have h7 : a ≠ b := by
        by_contra h8
        have h9 : a = b := by linarith
        have h10 : a ^ 2 = b ^ 2 := by
          rw [h9]
        have h11 : abs a = abs b := by
          rw [show b = a by linarith [h9]]
        tauto
      have eq6 : a ^ 3 - b ^ 3 = 0 := by linarith [h4]
      have eq7 : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
      rw [eq7] at eq6
      have eq8 : a - b ≠ 0 := by
        intro h13
        have h14 : a = b := by linarith
        have h15 : abs a = abs b := by
          rw [show b = a by linarith [h14]]
        tauto
      have eq9 : a ^ 2 + a * b + b ^ 2 = 0 := by
        apply (mul_left_inj' eq8).mp
        linarith
      linarith
    -- Now eq5: a^2 + a * b + b^2 = 0
    -- But from eq2: a^2 = 2 * b^2
    have eq10 : 3 * b ^ 2 + a * b = 0 := by
      nlinarith [eq2, eq5]
    have eq11 : b * (3 * b + a) = 0 := by
      linarith [eq10]
    cases' (mul_eq_zero.mp eq11) with h12 h13
    · 
      exfalso
      exact hb (by linarith)
    · 
      -- 3 * b + a = 0
      -- So a = -3 * b
      -- From eq2: a^2 = 2 * b^2
      -- (-3 * b)^2 = 2 * b^2
      -- 9 * b^2 = 2 * b^2
      -- 7 * b^2 = 0
      -- So b^2 = 0
      -- So b = 0
      -- Contradiction with hb
      have eq14 : a = -3 * b := by linarith
      rw [eq14] at eq2
      have eq15 : 7 * b ^ 2 = 0 := by 
        nlinarith
      have eq16 : b ^ 2 = 0 := by
        linarith
      have eq17 : b = 0 := by
        nlinarith
      tauto

  have h5 : a ^ 3 + b ^ 3 ≠ 0 := by
    by_contra h5
    have eq4 : a ^ 3 = -b ^ 3 := by linarith
    have eq5 : a ^ 2 - a * b + b ^ 2 = 0 := by
      have h7 : a ≠ -b := by
        by_contra h8
        have h9 : a = -b := by linarith
        have h10 : abs a = abs b := by
          rw [show a = -b by linarith [h9]]
          rw [abs_neg]
        tauto
      have eq6 : a ^ 3 + b ^ 3 = 0 := by linarith [h5]
      have eq7 : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by ring
      rw [eq7] at eq6
      have eq8 : a + b ≠ 0 := by
        intro h13
        have h14 : a = -b := by linarith
        have h15 : abs a = abs b := by
          rw [show a = -b by linarith [h14]]
          rw [abs_neg]
        tauto
      have eq9 : a ^ 2 - a * b + b ^ 2 = 0 := by
        apply (mul_left_inj' eq8).mp
        linarith
      linarith
    -- Now eq5: a^2 - a * b + b^2 = 0
    -- But from eq2: a^2 = 2 * b^2
    have eq10 : 3 * b ^ 2 - a * b = 0 := by
      nlinarith [eq2, eq5]
    have eq11 : b * (3 * b - a) = 0 := by
      linarith [eq10]
    cases' (mul_eq_zero.mp eq11) with h12 h13
    · 
      exfalso
      exact hb (by linarith)
    · 
      -- 3 * b - a = 0
      -- So a = 3 * b
      -- From eq2: a^2 = 2 * b^2
      -- (3 * b)^2 = 2 * b^2
      -- 9 * b^2 = 2 * b^2
      -- 7 * b^2 = 0
      -- So b^2 = 0
      -- So b = 0
      -- Contradiction with hb
      have eq14 : a = 3 * b := by linarith
      rw [eq14] at eq2
      have eq15 : 7 * b ^ 2 = 0 := by 
        nlinarith
      have eq16 : b ^ 2 = 0 := by
        linarith
      have eq17 : b = 0 := by
        nlinarith
      tauto

  have eq3 : a ^ 6 = 8 * b ^ 6 := by
    calc
      a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = (2 * b ^ 2) ^ 3 := by rw [eq2]
      _ = 8 * (b ^ 2) ^ 3 := by ring
      _ = 8 * b ^ 6 := by ring

  have eq4 : (a ^ 3 + b ^ 3) / (a ^ 3 - b ^ 3) + (a ^ 3 - b ^ 3) / (a ^ 3 + b ^ 3) = (18 / 7 : ℝ) := by
    have eq5 : (a ^ 3 + b ^ 3) / (a ^ 3 - b ^ 3) + (a ^ 3 - b ^ 3) / (a ^ 3 + b ^ 3) =
      ((a ^ 3 + b ^ 3) ^ 2 + (a ^ 3 - b ^ 3) ^ 2) / ((a ^ 3 + b ^ 3) * (a ^ 3 - b ^ 3)) := by
      field_simp [h4, h5]
      <;> ring
    rw [eq5]
    have eq6 : (a ^ 3 + b ^ 3) * (a ^ 3 - b ^ 3) = a ^ 6 - b ^ 6 := by
      ring
    have eq7 : a ^ 6 - b ^ 6 = 7 * b ^ 6 := by
      nlinarith [eq3]
    have eq8 : (a ^ 3 + b ^ 3) ^ 2 + (a ^ 3 - b ^ 3) ^ 2 = 18 * b ^ 6 := by
      have eq9 : (a ^ 3 + b ^ 3) ^ 2 + (a ^ 3 - b ^ 3) ^ 2 = 2 * (a ^ 6 + b ^ 6) := by
        ring_nf
      rw [eq9]
      have eq10 : a ^ 6 = 8 * b ^ 6 := eq3
      nlinarith [eq10]
    rw [eq6, eq7, eq8]
    have h6 : b ^ 6 ≠ 0 := by
      have hb2 : b ≠ 0 := hb
      exact pow_ne_zero 6 hb2
    field_simp [h6]
    <;> ring
  exact eq4