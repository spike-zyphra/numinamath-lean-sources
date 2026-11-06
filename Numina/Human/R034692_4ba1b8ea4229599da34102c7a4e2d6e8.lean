import Mathlib

/-The parabola $y = x^2 + bx + c$ has the following properties:

The point on the parabola closest to $(12,3)$ is the $y$-intercept of the parabola.
The parabola passes through $(-5,0).$

Enter the ordered pair $(b,c).$-/
theorem algebra_21730 {b c : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + b * x + c) : (IsMinOn (fun (x : ℝ × ℝ) => Real.sqrt ((x.1 - 12) ^ 2 + (x.2 - 3) ^ 2)) {x : ℝ × ℝ | x.2 = f x.1} ⟨0, f 0⟩) ∧  (f (-5) = 0) ↔ b = 6 ∧ c = 5 := by
  constructor
  intro ⟨h₁, h₂⟩
  -- Prove that the function $(x - 12) ^ 2 + (f x - 3) ^ 2$ have a minimum at $x = 0$
  · have h₃ : IsMinOn (fun (x : ℝ) => (x - 12) ^ 2 + (f x - 3) 
    ^ 2) Set.univ 0 := by
      rw [isMinOn_iff]
      rw [isMinOn_iff] at h₁
      intro x _
      have := h₁ ⟨x, f x⟩ (by simp)
      simp at this
      simp
      rw [← Real.sqrt_le_sqrt_iff]; exact this
      · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
    have h₄ := IsLocalMinOn.isLocalMin h₃.localize (by simp)
  -- Take derivative at the minimum point
    have h₅ := h₄.deriv_eq_zero
    have hdf : deriv f = fun x => 2 * x + b := by
      ext x; rw [hf]; simp; rw [deriv_add, deriv_pow, deriv_const_mul]; simp
      simp; apply DifferentiableAt.pow (by simp); apply DifferentiableAt.const_mul (by simp)
    have hdf₁ : ∀ x, DifferentiableAt ℝ f x := by
      intro x; rw [hf]; simp; apply DifferentiableAt.const_mul; simp
    rw [deriv_add, deriv_pow'', deriv_pow''] at h₅
  --Compute the derivative
    simp at h₅; rw [deriv_sub, hdf, hf] at h₅; simp at h₅
    rw [hf] at h₂; simp at h₂; ring_nf at h₂
  --from f(-5)=0 we have c=5b-25
    have h₆ := eq_neg_of_add_eq_zero_right h₂
  -- Substitute h₆ into h₅
    rw [h₆] at h₅
    have : -(2 * 12) + 2 * (-(25 - b * 5) - 3) * b = 10 * (b + 2 / 5) * (b - 6) := by ring
    rw [this] at h₅
    rcases mul_eq_zero.mp h₅ with h₅ | h₅
    · rcases mul_eq_zero.mp h₅ with h₅ | h₅
      · norm_num at h₅
    --Verifying the case b=-2/5
      have h₇ := eq_neg_of_add_eq_zero_left h₅
      rw [isMinOn_iff] at h₃
      have h₈ := h₃ 6 (by simp)
      rw [hf] at h₈; simp at h₈
      rw [h₆, h₇] at h₈
      norm_num at h₈
    rw [sub_eq_zero] at h₅
    rw [h₅] at h₆
    norm_num at h₆
    exact ⟨h₅, h₆⟩
    apply hdf₁; simp; simp [hdf₁]; simp; simp; simp [hdf₁]
-- Verifying the case b=6, c=5
  intro ⟨hb, hc⟩
  rw [isMinOn_iff]
  constructor
  · intro ⟨x, y⟩ hxy
    rw [Real.sqrt_le_sqrt_iff (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simp [hf, hb, hc] at hxy
    simp [hf, hb, hc, hxy]
    rw [← sub_nonneg]
    ring_nf
    have : x ^ 2 * 41 + x ^ 3 * 12 + x ^ 4 = x ^ 2 * ((x + 6) ^ 2 + 5) := by ring
    rw [this]
    apply mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (by norm_num))
  simp [hf, hb, hc]; norm_num