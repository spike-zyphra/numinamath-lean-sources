import Mathlib

theorem algebra_245950 {a b c : ℝ} (h1 : a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c = 1)
    (h2 : b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c = 1) (h3 : c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have eq1 : (a - b) * ((a - b) ^ 2 + 3 * c ^ 2) = 0 := by 
    nlinarith 
  have eq2 : (b - c) * ((b - c) ^ 2 + 3 * a ^ 2) = 0 := by 
    nlinarith 
  have eq3 : (a - c) * ((a - c) ^ 2 + 3 * b ^ 2) = 0 := by 
    nlinarith 
  have h4 : a - b = 0 := by 
    cases' (mul_eq_zero.mp eq1) with h41 h42
    · -- Case where a - b = 0
      linarith 
    · -- Case where (a - b) ^ 2 + 3 * c ^ 2 = 0
      have h5 : (a - b) ^ 2 + 3 * c ^ 2 = 0 := by linarith 
      have h6 : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg 
      have h7 : 3 * c ^ 2 ≥ 0 := by nlinarith [sq_nonneg c] 
      have h8 : (a - b) ^ 2 = 0 := by nlinarith 
      have h9 : c ^ 2 = 0 := by nlinarith 
      have h10 : a - b = 0 := by nlinarith 
      have h11 : c = 0 := by nlinarith 
      nlinarith [sq_nonneg (c ^ 2), sq_nonneg (c ^ 2)]
  -- We have a - b = 0 
  have h5 : b - c = 0 := by 
    cases' (mul_eq_zero.mp eq2) with h51 h52
    · -- Case where b - c = 0
      linarith 
    · -- Case where (b - c) ^ 2 + 3 * a ^ 2 = 0
      have h6 : (b - c) ^ 2 + 3 * a ^ 2 = 0 := by linarith 
      have h7 : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg 
      have h8 : 3 * a ^ 2 ≥ 0 := by nlinarith [sq_nonneg a] 
      have h9 : (b - c) ^ 2 = 0 := by nlinarith 
      have h10 : a ^ 2 = 0 := by nlinarith 
      have h11 : b - c = 0 := by nlinarith 
      have h12 : a = 0 := by nlinarith 
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (c ^ 2), h12]
  -- We have a - b = 0 and b - c = 0 
  have h6 : a - c = 0 := by 
    nlinarith [h4, h5] 
  -- Therefore $a = b = c$.
  have ha1 : a = 1 := by 
    have h7 : a ^ 3 = 1 := by 
      have h8 : a = b := by linarith [h4] 
      have h9 : b = c := by linarith [h5] 
      rw [show b = a by nlinarith] at h1 
      rw [show c = a by nlinarith] at h1 
      nlinarith 
    have ha1 : a = 1 := by 
      have h10 : a ^ 3 - 1 = 0 := by linarith 
      have h11 : (a - 1) * (a ^ 2 + a + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h11) with h12 h13 
      · -- Either a - 1 = 0, so a = 1 
        linarith 
      · -- Or a^2 + a + 1 = 0 
        nlinarith [sq_nonneg (a + 1 / 2)]
    exact_mod_cast ha1 
  -- Therefore $a = 1$
  have hb1 : b = 1 := by 
    linarith [show a = 1 by linarith [ha1], h4]
  have hc1 : c = 1 := by 
    linarith [show b = 1 by linarith [hb1], h5]
  exact ⟨ha1, hb1, hc1⟩