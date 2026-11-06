import Mathlib

theorem algebra_19710 {f: ℝ → ℝ}{k: ℝ → ℝ}
  (hf : ∀ x, x > 0 → f x = k x)
  (hf' : ∀ x, x < 0 → f x = -1 / (2 * x))
  (hf'' : ∀ x, x = 0 → f x = 0):
  (∀x, f (f x) = x) ↔ (∀x, x > 0 → k x = -1/(2*x)) := by
  constructor
  · -- Assume that ∀x, f (f x) = x, prove that ∀x>0, k x = -1/(2*x)
    intro h
    intro x hx
    have h1 := h (-1 / (2 * x))
    have h2 : -1 / (2 * x) < 0 := by
      apply div_neg_of_neg_of_pos
      norm_num
      all_goals linarith
    have h3 : f (-1 / (2 * x)) = x := by
      rw [hf' (-1 / (2 * x)) h2]
      field_simp [show x ≠ 0 from ne_of_gt hx]
    have h4 : f (f (-1 / (2 * x))) = -1 / (2 * x) := h (-1 / (2 * x))
    rw [h3] at h4
    have h5 : x > 0 := hx
    have h6 : f x = k x := by
      apply hf x h5
    have h7 : k x = -1 / (2 * x) := by
      have h8 : f x = -1 / (2 * x) := by
        linarith [h4, h6]
      have h9 : k x = -1 / (2 * x) := by
        have h10 : f x = k x := by
          apply hf x h5
        linarith
      linarith
    linarith
  · -- Assume that ∀x>0, k x = -1/(2*x), prove that ∀x, f (f x) = x
    intro hk
    intro x
    by_cases h1 : x > 0
    · -- Case x > 0.
      have hx1 : f x = -1 / (2 * x) := by
        have hx2 : f x = k x := hf x h1
        have hx3 : k x = -1 / (2 * x) := hk x h1
        linarith
      have hx2 : f (f x) = x := by
        rw [hx1]
        have hx6 : -1 / (2 * x) < 0 := by
          apply div_neg_of_neg_of_pos
          norm_num
          all_goals linarith
        rw [hf' (-1 / (2 * x)) hx6]
        field_simp [show x ≠ 0 from ne_of_gt (show x > 0 by linarith [h1])]
      linarith [hx2]
    by_cases h2 : x < 0
    · -- Case x < 0.
      have hx1 : f x = -1 / (2 * x) := hf' x h2
      have hx2 : f (f x) = x := by
        rw [hx1]
        have h6 : -1 / (2 * x) > 0 := by
          apply div_pos_of_neg_of_neg
          norm_num
          all_goals linarith
        have hx3 : f (-1 / (2 * x)) = k (-1 / (2 * x)) := by
          apply hf (-1 / (2 * x)) h6
        have hx4 : k (-1 / (2 * x)) = x := by 
          specialize hk (-1 / (2 * x)) (show -1 / (2 * x) > 0 by linarith [h6] )
          rw [hk]
          have h8 : x < 0 := h2
          field_simp [(show x ≠ 0 from by linarith)]
          <;> nlinarith
        rw [hx3]
        all_goals try linarith [hx4]
      linarith [hx2]
    · -- Case x = 0.
      have h1 : x = 0 := by linarith
      rw [h1]
      have hx1 : f 0 = 0 := by 
        apply hf'' 0 (rfl)
      rw [hx1]
      all_goals linarith [hf'' 0 (rfl), h1]