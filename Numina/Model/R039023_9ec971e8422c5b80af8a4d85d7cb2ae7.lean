import Mathlib

theorem algebra_11707 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y - 3)
    (hf : ∀ x > 0, f x < 3) (h6 : f 6 = -9) :
    f ((1 / 2) ^ 2010) = 3 - (1 / 2) ^ 2009 := by
  have f0 : f 0 = 3 := by
    have h00 := h 0 0
    norm_num at h00
    linarith
  have f2 : f (2 : ℝ) = -1 := by
    have h3 := h 2 2
    norm_num at h3
    have h4 : f 4 = 2 * (f 2) - 3 := by linarith
    have h5 := h 4 2
    norm_num at h5
    nlinarith [show f 6 = -9 from h6, h4]
  have f4 : f (1 : ℝ) = 1 := by
    have h3 := h 1 1
    norm_num at h3
    nlinarith [show f 2 = -1 by linarith [f2]]
  have f16 : f (1 / 2 : ℝ) = 2 := by
    have h0 := h (1 / 2 : ℝ) (1 / 2 : ℝ)
    norm_num at h0
    nlinarith [show f 1 = 1 by linarith [f4]]
  have eq1 : ∀ (n : ℕ), f ((1 / 2 : ℝ) ^ (n + 1 : ℕ)) = 3 - (1 / 2 : ℝ) ^ (n : ℕ) := by
    intro n
    induction n with
    | zero =>
      norm_num [show f (1 / 2 : ℝ) = 2 by linarith [f16]]
    | succ n ih =>
      have eq5 : f ((1 / 2 : ℝ) ^ (n + 1 + 1 : ℕ)) = (3 + f ((1 / 2 : ℝ) ^ (n + 1 : ℕ)))/ 2 := by
        have eqn := h ((1 / 2 : ℝ) ^ (n + 2 : ℕ)) ((1 / 2 : ℝ) ^ (n + 2 : ℕ))
        have h1 : ((1 / 2 : ℝ) ^ (n + 2 : ℕ)) + ((1 / 2 : ℝ) ^ (n + 2 : ℕ)) =
            ((1 / 2 : ℝ) ^ (n + 1 : ℕ)) := by 
          ring_nf
          <;> norm_num
        rw [h1] at eqn
        nlinarith [eqn]
      rw [eq5, ih]
      field_simp at *
      ring_nf at *
      <;> norm_num
      <;> linarith
      all_goals try { assumption <;> norm_num }
  specialize eq1 2009
  norm_num at eq1 ⊢
  all_goals
  linarith [eq1]