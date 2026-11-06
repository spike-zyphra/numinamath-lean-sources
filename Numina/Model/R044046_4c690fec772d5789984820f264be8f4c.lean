import Mathlib


open Real


theorem algebra_154218 {x y : ℝ} (hx : x ≠ 0) (h : x + 1/x = 2 * Real.cos y) (n : ℕ) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * y) := by
  have h1 : ∀ (n : ℕ), x ^ n + 1 / x ^ n = 2 * Real.cos (n * y) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num
      <;> simp [Real.cos_zero]
    | succ n =>
      cases n with
      | zero =>
        norm_num at *
        all_goals linarith [h]
      | succ k =>
        have h3 := ih k (by linarith)
        have h4 := ih (k + 1) (by linarith)
        have eq1 : x ^ (k + 2) + 1 / x ^ (k + 2) = (x + 1 / x) * (x ^ (k + 1) + 1 / x ^ (k + 1)) - (x ^ k + 1 / x ^ k) := by
          field_simp [hx]
          ring
        rw [eq1]
        rw [h4, h3, h]
        have eq12 : (2 * Real.cos y) * (2 * Real.cos ((↑k + 1 : ℝ) * y)) - (2 * Real.cos (↑k * y)) = 2 * Real.cos ((↑k + 1 + 1 : ℝ) * y) := by
          have eq5 : 2 * Real.cos ((↑k + 1 + 1 : ℝ) * y) = 4 * Real.cos y * Real.cos ((↑k + 1 : ℝ) * y) - 2 * Real.cos (↑k * y) := by
            have h7 : Real.cos ((↑k + 1 + 1 : ℝ) * y) = Real.cos ((↑k + 1 : ℝ) * y + y) := by
              ring_nf
            have h8 : Real.cos ((↑k + 1 : ℝ) * y + y) = Real.cos ((↑k + 1 : ℝ) * y) * Real.cos y - Real.sin ((↑k + 1 : ℝ) * y) * Real.sin y := by
              rw [Real.cos_add]
            have h9 : Real.cos (↑k * y) = Real.cos ((↑k + 1 : ℝ) * y - y) := by
              ring_nf
            have h10 : Real.cos ((↑k + 1 : ℝ) * y - y) = Real.cos ((↑k + 1 : ℝ) * y) * Real.cos y + Real.sin ((↑k + 1 : ℝ) * y) * Real.sin y := by
              rw [Real.cos_sub]
            rw [h7, h8, show Real.cos (↑k * y) = Real.cos ((↑k + 1 : ℝ) * y - y) by 
              rw [show Real.cos ((↑k + 1 : ℝ) * y - y) = Real.cos (↑k * y) by 
                ring_nf
              ]
            ]
            have h11 : Real.cos ((↑k + 1 : ℝ) * y + y) + Real.cos ((↑k + 1 : ℝ) * y - y) = 2 * Real.cos ((↑k + 1 : ℝ) * y) * Real.cos y := by
              rw [h8, h10]
              ring
            nlinarith
          linarith [eq5]
        field_simp at eq12 ⊢
        ring_nf at eq12 ⊢
        nlinarith [eq12]
  specialize h1 n
  simpa using h1