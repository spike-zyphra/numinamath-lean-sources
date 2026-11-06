import Mathlib

theorem number_theory_52077 : ¬∃ (x y : ℤ), x > 0 ∧ y > 0 ∧ x ^ 3 + 11 ^ 3 = y ^ 3 := by
  rintro ⟨x, y, hx, hy, h⟩
  have h1 : y > x := by
    by_contra h2
    push_neg at h2
    have h3 : x ≥ y := by linarith
    have h4 : x ^ 3 ≥ y ^ 3 := by
      have h5 : x ≥ y := h3
      have h6 : x ^ 2 ≥ y ^ 2 := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
      have h7 : x ^ 3 ≥ y ^ 3 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
      linarith
    have h8 : x ^ 3 + 11 ^ 3 ≥ y ^ 3 := by nlinarith [h4]
    nlinarith [show 0 < 11 by norm_num]
  have h2 : (y - x) * (y ^ 2 + y * x + x ^ 2) = 11 ^ 3 := by
    nlinarith [h]
  have h4 : (y - x) ∣ 11 ^ 3 := by
    use y ^ 2 + y * x + x ^ 2
    all_goals linarith [h2]
  have h5 : (y - x) = 1 ∨ (y - x) = 11 ∨ (y - x) = 11 ^ 2 ∨ (y - x) = 11 ^ 3 := by
    have h9 : (y - x) ∣ 11 ^ 3 := h4
    have h12 : (y - x) = 1 ∨ (y - x) = 11 ∨ (y - x) = 11 ^ 2 ∨ (y - x) = 11 ^ 3 := by
      have h13 : (y - x) ∣ 11 ^ 3 := h9
      -- y - x is positive since y > x
      have h10 : (y - x) ≥ 1 := by
        nlinarith
      -- y - x divides 1331 = 11^3
      have h15 : (y - x) ≤ 1331 := by
        exact Int.le_of_dvd (by norm_num) h13
      interval_cases k : (y - x) <;> norm_num at h13 ⊢ 
      all_goals 
        tauto
    exact h12
  rcases h5 with (h7 | h7 | h7 | h7)
  · -- case $y - x = 1$
    have eq1 : y = x + 1 := by linarith
    rw [eq1] at h2
    ring_nf at h2
    have h11 : x ≤ 22 := by nlinarith
    have h12 : x ≥ -22 := by nlinarith
    interval_cases x <;> omega
  · -- case $y - x = 11$
    have eq1 : y = x + 11 := by linarith
    rw [eq1] at h2
    ring_nf at h2
    have h10 : x = 0 ∨ x = -11 := by
      have h11 : x * (x + 11) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h11) with
      | inl h12 => 
        have h12' : x = 0 := by nlinarith
        tauto
      | inr h13 => 
        have h14' : x + 11 = 0 := by nlinarith
        have h15' : x = -11 := by linarith
        tauto
    cases h10 with
    | inl h11 => 
      nlinarith
    | inr h11 => 
      nlinarith
  · -- case $y - x = 11^2$
    have eq1 : y = x + 11 ^ 2 := by linarith
    rw [eq1] at h2
    ring_nf at h2
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x - 0)]
  · -- case $y - x = 11^3$
    have eq1 : y = x + 11 ^ 3 := by linarith
    rw [eq1] at h2
    ring_nf at h2
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x - 0)]