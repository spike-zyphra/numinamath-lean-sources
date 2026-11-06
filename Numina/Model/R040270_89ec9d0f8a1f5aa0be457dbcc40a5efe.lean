import Mathlib

theorem algebra_280110 {a b : ℕ → ℝ} {q : ℝ} (hq : q ≠ 1)
    (ha : ∀ n, a n = a 0 * q ^ n) (hb1 : b 1 = a 0 + a 1 + a 2)
    (hb2 : b 2 = a 3 + a 4 + a 5) (hb3 : b 3 = a 6 + a 7 + a 8)
    (hb : ∀ n, b n = a (3 * n - 2) + a (3 * n - 1) + a (3 * n)) :
    ∃ r, ∀ n, b (n + 1) = r * b n := by

  have eq1 : a 0 = a 3 := by
    have eq2 : b 1 = a (3 * 1 - 2) + a (3 * 1 - 1) + a (3 * 1) := by
      apply hb 1
    have eq3 : b 1 = a 0 + a 1 + a 2 := hb1
    norm_num at eq2 eq3 
    linarith

  have h1 : a 3 = a 0 * q ^ 3 := by
    specialize ha 3
    simpa using ha

  have h2 : a 0 = 0 := by
    have eq3 : a 0 = a 3 := eq1
    rw [h1] at eq3
    have h3 : a 0 * (q ^ 3 - 1) = 0 := by 
      linarith

    cases' (mul_eq_zero.1 h3) with h4 h5
    · 
      linarith 
    · 
      have hq3 : q ^ 3 = 1 := by linarith 
      have h3 : q = 1 := by
        have h4 : q ^ 3 - 1 = 0 := by linarith
        have h5 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
        rw [h5] at h4 
        cases' (mul_eq_zero.1 h4) with h6 h7
        · 
          have : q = 1 := by linarith
          linarith 
        · 
          have h23 : q ^ 2 + q + 1 = 0 := by linarith 
          nlinarith [sq_nonneg (q + 1 / 2)]
      tauto

  use 0 
  intro n 
  have h3 : ∀ (n : ℕ), a n = 0 := by
    intro n 
    specialize ha n 
    rw [show a 0 = (0 : ℝ) by linarith [h2]] at ha 
    simp at ha ⊢ 
    try linarith

  have h4 : ∀ (n : ℕ), b n = 0 := by 
    intro n 
    specialize hb n 
    rw [hb]
    have eq1 : a (3 * n - 2) = 0 := h3 (3 * n - 2)
    have eq2 : a (3 * n - 1) = 0 := h3 (3 * n - 1)
    have eq3 : a (3 * n) = 0 := h3 (3 * n)
    linarith

  have eq1 : b (n + 1) = 0 := by 
    apply h4 (n + 1)
  have eq2 : b n = 0 := by 
    apply h4 n 
  simp [eq1, eq2]