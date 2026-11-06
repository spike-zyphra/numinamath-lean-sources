import Mathlib

theorem algebra_195373 {x y z r : ℝ} (hy : y = x * r) (hz : z = y * r) (hxy : x ≠ y)
    (hseq : ∃ d, x + d = 2 * y ∧ 2 * y + d = 3 * z) :
    r = 1 / 3 := by
  rcases hseq with ⟨d, hd₁, hd₂⟩
  have h₁ : 3 * z = 4 * y - x := by
    linarith
  rw [hz] at h₁
  rw [hy] at h₁
  have h₂ : x * (3 * r^2 - 4 * r + 1) = 0 := by
    ring_nf at h₁ ⊢
    nlinarith
  cases (mul_eq_zero.mp h₂) with
  | inl h₃ =>
    -- From h₃: x = 0
    have h₀ : y = 0 := by
      rw [hy]
      rw [h₃]
      all_goals nlinarith
      <;> ring
    have h₄ : x = 0 := by linarith
    have h₅ : x = y := by
      linarith [h₄, h₀]
    contradiction
  | inr h₄ =>
    -- From h₄: 3 * r^2 - 4 * r + 1 = 0 
    have h₅ : 3 * r ^ 2 - 4 * r + 1 = 0 := by
      linarith
    have h₆ : (r - 1) * (3 * r - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h₆) with
    | inl h₇ =>
      -- Case: r - 1 = 0 → r = 1
      have h₈ : r = 1 := by linarith
      have h₁₀ : y = x := by
        rw [hy, h₈]
        all_goals ring_nf
        <;> nlinarith
      have h₁₁ : x = y := by
        linarith [h₁₀]
      contradiction
    | inr h₈ =>
      -- Case: 3 * r - 1 = 0 → r = 1/3
      have h₉ : r = 1 / 3 := by
        linarith
      exact h₉