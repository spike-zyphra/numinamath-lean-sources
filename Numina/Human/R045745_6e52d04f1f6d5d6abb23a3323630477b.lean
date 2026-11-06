import Mathlib

/- 4. If the system of inequalities about $x$ $\left\{\begin{array}{l}x^{3}+3 x^{2}-x-3>0, \\ x^{2}-2 a x-1 \leqslant 0\end{array} \quad(a>0)\right.$ has exactly one integer solution, then the range of values for $a$ is $\qquad$.-/
theorem inequalities_152982 :
    {a : ℝ | 0 < a ∧ ∃! x : ℤ, x ^ 3 + 3 * x ^ 2 - x - 3 > 0 ∧ x ^ 2 - 2 * a * x - 1 ≤ 0} = Set.Ico (3 / 4) (4 / 3) := by
  -- Show that x ^ 3 + 3 * x ^ 2 - x - 3 > 0 if and only if x = -2 or x ≥ 2.
  have hlm (x : ℤ) : x ^ 3 + 3 * x ^ 2 - x - 3 > 0 ↔ x = -2 ∨ x ≥ 2 := by
    rw [show x ^ 3 + 3 * x ^ 2 - x - 3 = (x + 3) * (x + 1) * (x - 1) by ring]
    constructor
    . intro h₀
      -- Show that x ≥ -2.
      have h₃ : x ≥ -2 := by
        by_contra!
        -- Show that x ≠ -3, so x ≤ -4.
        have h₃ : x ≠ -3 := by
          by_contra! h₃
          norm_num  [h₃] at h₀
        replace h₃ : x ≤ -4 := by
          omega
        -- Show that this contradicts with (x + 3)(x + 1)(x - 1) > 0.
        have h₄ : (-x - 3) * (-x - 1) * (-x + 1) > 0 := by
          iterate 2 apply mul_pos
          all_goals
            omega
        linarith only [h₀, h₄]
      -- Show that x ≠ -1, 0, 1.
      have h₄ : ¬(x = -1 ∨ x = 0 ∨ x = 1) := by
        by_contra! h₄
        rcases h₄ with (h₄ | h₄ | h₄)
        <;> norm_num [h₄] at h₀
      omega
    . rintro (hx | hx)
      . norm_num [hx]
      . iterate 2 apply mul_pos
        all_goals
          omega
  -- Break the goal into two parts.
  ext a
  constructor
  . -- Show that if such system of inequalities has only one integer solution for a > 0, then a ∈ [3 / 4, 4 / 3).
    rintro ⟨ha, ⟨x, ⟨h₀, h₁⟩, h₂⟩⟩
    simp
    by_contra h₃
    rw [Classical.not_and_iff_or_not_not] at h₃
    push_neg at h₃
    rcases h₃ with (h₃ | h₃)
    . -- Suppose that 0 < a < 3 / 4, we show that there are no integer solution x.
      rw [hlm] at h₀
      rcases h₀ with (h₀ | h₀)
      . -- Show that x = -2 gives contradiction.
        norm_num [h₀] at h₁
        linarith
      . -- Show that x ≥ 2 gives contradiction.
        replace h₀ : x ≥ 2 := by
          omega
        replace h₁ : (2 - a) ^ 2 ≤ a ^ 2 + 1 := by
          calc
            _ ≤ (x - a) ^ 2 := by
              rify at h₀
              rw [sq_le_sq₀]
              <;> linarith
            _ ≤ a ^ 2 + 1 := by
              linarith
        linarith
    . -- Suppose that a ≥ 4 / 3, we show that there are at least two integer solutions x, hence contradiction.
      linarith only [h₂ 2 (by simp; linarith), h₂ 3 (by simp; linarith)]
  . -- Show that if a ∈ [3 / 4, 4 / 3), then there is only one integer solution for the system of inequalities.
    rintro ⟨h₀, h₁⟩
    simp [show 0 < a by positivity]
    -- Show that x = 2 is the only integer solution.
    use 2
    constructor
    . -- Show that x = 2 is a solution.
      simp
      linarith
    . -- Show that x = 2 is the only solution.
      rintro y ⟨h₂, h₃⟩
      -- Suppose that there is some solution y ≠ 2.
      rw [<-sub_pos, <-gt_iff_lt, hlm] at h₂
      by_contra! h₄
      rcases h₂ with (h₂ | h₂)
      . -- Show that y = -2 gives contradiction.
        norm_num [h₂] at h₃
        linarith
      . -- Show that y ≥ 3 gives contradiction.
        replace h₂ : y ≥ 3 := by
          omega
        replace h₃ : (3 - a) ^ 2 ≤ a ^ 2 + 1 := by
          calc
            _ ≤ (y - a) ^ 2 := by
              rify at h₂
              rw [sq_le_sq₀]
              <;> linarith
            _ ≤ a ^ 2 + 1 := by
              linarith
        linarith

