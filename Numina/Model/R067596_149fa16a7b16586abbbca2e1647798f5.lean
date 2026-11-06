import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12477 {f : ℝ → ℝ → ℝ} (hf : ∀ a, f a = λ x => a * sin x - 1 / 2 * cos (2 * x) + a - 3 / a + 1 / 2)
  (a : ℝ) (ha : a ≠ 0) (h : 2 ≤ a) :
  (∃ x, f a x ≤ 0) ↔ 2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Forward direction: existence of x with f a x ≤ 0 implies 2 ≤ a ∧ a ≤ 3
    intro ⟨x, hx⟩
    have f_def : f a x = a * sin x - 1 / 2 * cos (2 * x) + a - 3 / a + 1 / 2 := by
      rw [hf]
    rw [f_def] at hx
    have h₁ : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
      rw [cos_two_mul]
      rw [sin_sq]
      ring
    rw [h₁] at hx
    have h₂ : a * sin x + sin x ^ 2 + a - 3 / a ≤ 0 := by
      nlinarith
    have h₃ : -1 ≤ sin x ∧ sin x ≤ 1 := sin_mem_Icc x
    have h₅ : 1 - 3 / a ≤ 0 := by
      nlinarith [sq_nonneg (sin x + 1), sq_nonneg (a - 3), h, h₃.right, h₃.left, 
          sq_pos_of_ne_zero ha, 
          sq_nonneg (sin x), 
          sq_nonneg (a * sin x + sin x ^ 2 + a - 3 / a)
          ]
    have h₆ : a ≤ 3 := by 
      have h₇ : 1 - 3 / a ≤ 0 := h₅
      have h₈ : 1 ≤ 3 / a := by linarith 
      have h₉ : a > 0 := by nlinarith 
      have h₁₀ : a ≤ 3 := by 
        have h₁₁ : 1 ≤ 3 / a := h₈
        apply (le_div_iff₀ (by positivity)).mp at h₁₁ 
        nlinarith
      exact h₁₀
    exact ⟨by linarith, by linarith⟩
  · -- Reverse direction: 2 ≤ a ∧ a ≤ 3 implies ∃ x, f a x ≤ 0
    rintro ⟨h₁, h₂⟩
    use -(Real.pi / 2)
    have h₃ : f a (- (Real.pi / 2)) = a * sin (- (Real.pi / 2)) - 1 / 2 * cos (2 * (- (Real.pi / 2))) + a - 3 / a + 1 / 2 := by 
      rw [hf]
    rw [h₃]
    have h₄ : sin (- (Real.pi / 2)) = -1 := by
      rw [sin_neg]
      rw [sin_pi_div_two]
      all_goals ring
    have h₅ : cos (2 * (- (Real.pi / 2))) = -1 := by
      have h₆ : 2 * (- (Real.pi / 2)) = -Real.pi := by 
        ring_nf
      rw [h₆]
      have h₇ : cos (-Real.pi) = cos Real.pi := by
        rw [cos_neg]
      rw [h₇]
      norm_num [Real.cos_pi]
    rw [h₄, h₅]
    have h₃ : a > 0 := by nlinarith
    have h₄ : 1 - 3 / a ≤ 0 := by
      have h₅ : a ≤ 3 := h₂
      have h₆ : 3 / a ≥ 1 := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    nlinarith