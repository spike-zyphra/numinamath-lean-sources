import Mathlib

theorem algebra_327038 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : ∀ x, f (x + 2) = f (-x + 2)) (h2 : f 0 = 1) (h3 : ∃ x y, x ≠ y ∧ f x = 0 ∧ f y = 0 ∧ |x - y| = 2 * Real.sqrt 2) :
    f = fun x => (1 / 2) * (x - 2) ^ 2 - 1 := by

  rcases hf with ⟨a, b, c, h_def⟩
  have h_f0 : a * (0 : ℝ) ^ 2 + b * (0 : ℝ) + c = 1 := by
    rw [h_def] at h2
    simpa using h2
  have hc : c = 1 := by 
    linarith

  have h4 : b = -4 * a := by 
    have eq1 := h1 0 
    simp [h_def] at eq1 
    have eq2 := h1 1
    simp [h_def] at eq2 
    linarith

  rcases h3 with ⟨x, y, hxy, hx0, hy0, hxy_len⟩
 
  have eq1 : a * x ^ 2 + b * x + c = 0 := by 
    rw [h_def] at hx0 
    simpa using hx0 
  have eq2 : a * y ^ 2 + b * y + c = 0 := by 
    rw [h_def] at hy0 
    simpa using hy0

  rw [show c = 1 by linarith [hc], show b = -4 * a by linarith [h4]] at eq1
  rw [show c = 1 by linarith [hc], show b = -4 * a by linarith [h4]] at eq2

  have eq3 : a * (x ^ 2 - y ^ 2) - 4 * a * (x - y) = 0 := by
    nlinarith

  have eq4 : a * (x - y) * (x + y - 4) = 0 := by
    ring_nf at eq3 ⊢ 
    linarith

  have h5 : x - y ≠ 0 := by 
    intro h 
    apply hxy 
    linarith

  have h7 : x + y - 4 = 0 := by 
    cases' (mul_eq_zero.mp eq4) with h9 h10
    cases' (mul_eq_zero.mp h9) with h11 h12 
    · -- Case a = 0 
      exfalso 
      have ha : a = 0 := by 
        linarith 
      rw [ha] at eq1 
      nlinarith 
    · -- Case x - y = 0 
      exfalso 
      have h7 : x - y = 0 := by 
        linarith 
      contradiction 
    · -- Case x + y - 4 = 0 
      linarith

  have eq77 : x + y = 4 := by
    linarith

  have eq88 : (x - y) ^ 2 = 8 := by
    have h_eq : |x - y| = 2 * Real.sqrt 2 := hxy_len 
    calc 
      (x - y) ^ 2 = ( |x - y| ) ^ 2 := by 
        rw [sq_abs] 
      _ = (2 * Real.sqrt 2) ^ 2 := by 
        rw [h_eq] 
      _ = 4 * (Real.sqrt 2) ^ 2 := by 
        ring 
      _ = 4 * 2 := by 
        rw [Real.sq_sqrt] 
        norm_num 
      _ = 8 := by 
        ring

  have h9 : x * y = 2 := by
    have h99 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by 
      nlinarith 
    rw [show (x + y) ^ 2 = 16 by
      rw [show x + y = 4 by linarith]
      norm_num 
    ] at h99 
    nlinarith

  have ha2 : a = 1 / 2 := by 
    have h11 : a * (x ^ 2 + y ^ 2) - 4 * a * (x + y) + 2 = 0 := by 
      nlinarith 
    have h12 : x ^ 2 + y ^ 2 = 12 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 2), eq88, h9] 
    rw [show x + y = 4 by linarith] at h11 
    rw [h12] at h11 
    linarith

  have hb : b = -2 := by
    rw [show a = 1 / 2 by linarith [ha2] ] at h4 
    linarith

  funext t 
  simp [h_def, ha2, hb, hc] 
  all_goals ring