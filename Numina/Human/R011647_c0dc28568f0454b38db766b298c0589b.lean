import Mathlib

open Real Set

/- Given $\alpha, \beta \in\left(0, \frac{\pi}{2}\right)$, then $\alpha+\beta=\frac{\pi}{2}$ if and only if: $\frac{\sin ^{3} \alpha}{\cos \beta}+\frac{\cos ^{3} \alpha}{\sin \beta}=1$. The necessity is obvious. -/
theorem algebra_140261 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2)) :
    α + β = Real.pi / 2 ↔ (Real.sin α ^ 3 / Real.cos β + Real.cos α ^ 3 / Real.sin β = 1) := by
  -- 0 < cos x for any x ∈ (0, π / 2).
  have hcos_pos {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    simp only [mem_Ioo] at hx ⊢
    constructor <;> linarith
  -- 0 < sin x for any x ∈ (0, π / 2).
  have hsin_pos {x : ℝ} (hx : x ∈ Ioo 0 (π / 2)) : 0 < sin x := by
    apply sin_pos_of_mem_Ioo
    simp only [mem_Ioo] at hx ⊢
    constructor <;> linarith
  constructor
  -- Show that α + β = π / 2 implies that sin α^3 / cos β + cos α^3 / sin β = 1.
  · intro h
    -- We have α = π / 2 - β, sin (π / 2 - β) = cos β and cos (π / 2 - β) = sin β
    rw [show α = π / 2 - β by linarith, sin_pi_div_two_sub, cos_pi_div_two_sub]
    rw [show 3 = 1 + 2 by norm_num, pow_add, pow_add, pow_one, pow_one]
    rw [mul_div_cancel_left₀ _ (ne_of_gt (hcos_pos h₁))]
    rw [mul_div_cancel_left₀ _ (ne_of_gt (hsin_pos h₁))]
    -- Simplify the goal and get sin β^2 + cos β^2 = 1.
    rw [add_comm, sin_sq_add_cos_sq]
  -- Suppose that sin α^(k+2) / cos β^k + cos α^(k+2) / sin β^k = 1 and show that α + β = π / 2.
  intro h
  -- Prove the following inequality for all 0 < x and 0 < y:
  -- 2 * x ^ 2 ≤ x ^ 3 / y + x * y.
  have hineq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 2 * x ^ 2 ≤ x ^ 3 / y + x * y := by
    field_simp
    rw [le_div_iff₀ hy, ← sub_nonneg]
    suffices 0 ≤ x * (x - y) ^ 2 by linear_combination this
    positivity
  -- Derive the following inequality:
  -- 2 ≤ sin (α + β) + 1.
  replace hineq : 2 ≤ sin (α + β) + 1 := by
    -- Use hineq with x = sin α and y = cos β and get
    -- 2 * sin α ^ 2 ≤ sin α ^ 3 / cos β + sin α * cos β.
    have h1 := hineq (hsin_pos h₀) (hcos_pos h₁)
    -- Use hineq with x = cos α and y = sin β and get
    -- 2 * cos α ^ 2 ≤ cos α ^ 3 / sin β + cos α * sin β.
    have h2 := hineq (hcos_pos h₀) (hsin_pos h₁)
    calc
      -- We have 2 = 2 * (sin α ^ 2 + cos α ^ 2)
      --           ≤ (sin α ^ 3 / cos β + cos α ^ 3 / sin β) + sin (α + β)
      -- (from h1 and h2 and from sin (α + β) = sin α * cos β + cos α * sin β)
      --           = sin (α + β) + 1
      -- (because sin α ^ 3 / cos β + cos α / sin β = 1).
      2 = 2 * (sin α ^ 2 + cos α ^ 2) := by rw [sin_sq_add_cos_sq, mul_one]
      _ ≤ (sin α ^ 3 / cos β + sin α * cos β) + (cos α ^ 3 / sin β + cos α * sin β) := by
          linear_combination h1 + h2
      _ = (sin α ^ 3 / cos β + cos α ^ 3 / sin β) + sin (α + β) := by
          rw [sin_add]; ring
      _ = sin (α + β) + 1 := by rw [h]; ring
  -- 2 ≤ sin (α + β) + 1 implies that 1 ≤ sin (α + β). But sin (α + β) ≤ 1 so sin (α + β) = 1.
  have hsin : sin (α + β) = 1 := by linarith [sin_le_one (α + β)]
  -- From sin (α + β) = 1 we obtain α + β = π / 2 + k * (2π) for some integer k.
  -- Show that k = 0.
  rw [sin_eq_one_iff] at hsin
  clear * - h₀ h₁ hsin
  have ⟨k, hk⟩ := hsin
  simp at h₀ h₁
  rcases show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega with h | h | h
  -- If k ≤ -1 then α + β < 0, a contradiction.
  · rify at h
    nlinarith
  · subst k
    linarith
  -- If 1 ≤ k then α + β > π, a contradiction.
  · rify at h
    nlinarith