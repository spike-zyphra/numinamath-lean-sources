import Mathlib

theorem algebra_316776 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = 2 * a n / (a n + 1)) :
    (∃ r, ∀ n, 1 / a n - 1 = r ^ n) ∧
    (∀ n, a n = 2 / (r ^ n + 1)) ∧
    (∑ i in Finset.Icc 1 n, a i * (a i - 1) < 3) := by
  have h1 := han 0
  norm_num [ha1] at h1
  have h4 : a 0 + 1 ≠ 0 := by 
    by_contra h5
    have h6 : a 0 = -1 := by 
      linarith
    rw [show a 0 = (-1 : ℝ) by linarith [h6]] at h1 
    norm_num at h1 
    all_goals 
      try { tauto } <;> try { nlinarith } <;> try { tauto } <;> try { nlinarith }
  -- From h1 we need to derive a contradiction
  have h7 : 2 * (a 0 + 1) = 2 * a 0 := by 
    have h8 : a 0 + 1 ≠ 0 := h4 
    have h9 : 2 = 2 * a 0 / (a 0 + 1) := by 
      linarith [h1]
    have h10 : 2 * (a 0 + 1) = 2 * a 0 := by
      have h11 : a 0 + 1 ≠ 0 := h4 
      field_simp [h11] at h9 ⊢ 
      <;> try { nlinarith } 
      all_goals try { tauto } 
    linarith [h10]
  -- This implies 2 = 0, a contradiction.
  have h13 : (2 : ℝ) = 0 := by 
    nlinarith 
  -- From 2 = 0, we can prove anything.
  exfalso 
  linarith [h13]