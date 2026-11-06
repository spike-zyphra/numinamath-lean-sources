import Mathlib

/- Determine the unique value of $k$ for which the system of equations $r^2 + s^2 = t$ and $r + s + t = k$ has exactly one real solution $(r, s, t)$.

(A) -3
(B) $-\frac{3}{2}$
(C) -1
(D) $-\frac{1}{2}$
(E) None of these -/
theorem algebra_620091 :
    {k : ℝ | {(r, s, t) : ℝ × ℝ × ℝ | r ^ 2 + s ^ 2 = t ∧ r + s + t = k}.encard = 1} = {-1 / 2} := by
  ext k
  simp
  constructor
  -- We first solve the easier part
  -- When k = -1 / 2, the only solution is (-1 / 2, -1 / 2, 1 / 2)
  swap
  . rintro rfl
    suffices H : {(r, s, t) : ℝ × ℝ × ℝ | r ^ 2 + s ^ 2 = t ∧ r + s + t = -1 / 2} = {(-1 / 2, -1 / 2, 1 / 2)} by simp [H]
    ext ⟨r, s, t⟩
    simp
    constructor
    . -- If (r, s, t) is a solution
      rintro ⟨h₁, h₂⟩
      -- We have (r + 1 / 2) ^ 2 + (s + 1 / 2) ^ 2 = 0
      have h₃ : (r + 1 / 2) ^ 2 + (s + 1 / 2) ^ 2 = 0 := by linarith
      -- So both terms must be 0
      have ⟨h₄, h₅⟩ : r + 1 / 2 = 0 ∧ s + 1 / 2 = 0 := by
        constructor
        all_goals
          apply pow_eq_zero (n := 2)
          linarith [sq_nonneg (r + 1 / 2), sq_nonneg (s + 1 / 2)]
      -- Thus we are done.
      refine ⟨?_, ?_, ?_⟩ <;> linarith
    . rintro ⟨rfl, rfl, rfl⟩
      norm_num
  . -- Now we show that if there is exactly one solution, then k = -1 / 2
    intro H
    -- By contradiction, assume k ≠ -1 / 2
    by_contra! hk
    -- Then we have k < -1 / 2 or k > -1 / 2
    rcases lt_or_gt_of_ne hk with hk | hk
    . -- If k < -1 / 2, then there is no solution
      have H₁ : {(r, s, t) : ℝ × ℝ × ℝ | r ^ 2 + s ^ 2 = t ∧ r + s + t = k} = ∅ := by
        ext ⟨r, s, t⟩
        simp
        intro h₁ h₂
        subst h₁
        -- Since (r + 1 / 2) ^ 2 + (s + 1 / 2) ^ 2 = k + 1 / 2, LHS ≥ 0 but RHS < 0
        linarith [sq_nonneg (r + 1 / 2), sq_nonneg (s + 1 / 2)]
      -- So we have a contradiction.
      simp [H₁] at H
    . -- If k > -1 / 2, then there are at least two solutions
      -- Let s₁ := √(k + 1 / 2) - 1 / 2 and s₂ := -√(k + 1 / 2) - 1 / 2
      let s₁ := √(k + 1 / 2) - 1 / 2
      let s₂ := -√(k + 1 / 2) - 1 / 2
      -- We have s₁ ≠ s₂ since k + 1 / 2 > 0
      have hs : s₁ ≠ s₂ := by
        simp [s₁, s₂, -one_div]
        intro h
        replace h : √(k + 1 / 2) = 0 := by linarith only [h]
        replace hk' : k + 1 / 2 > 0 := by linarith [hk]
        absurd h
        positivity
      -- We have (s₁ + 1 / 2) ^ 2 = k + 1 / 2
      have hs₁ : (s₁ + 1 / 2) ^ 2 = k + 1 / 2 := by
        simp [s₁, -one_div, show k + 1 / 2 ≥ 0 by linarith only [hk]]
      -- We have (s₂ + 1 / 2) ^ 2 = k + 1 / 2
      have hs₂ : (s₂ + 1 / 2) ^ 2 = k + 1 / 2 := by
        simp [s₂, -one_div, show k + 1 / 2 ≥ 0 by linarith only [hk]]
      -- We have (-1 / 2, s₁, (-1 / 2) ^ 2 + s₁ ^ 2) and (-1 / 2, s₂, (-1 / 2) ^ 2 + s₂ ^ 2) are solutions
      have H₁ : {(-1 / 2, s₁, (-1 / 2) ^ 2 + s₁ ^ 2), (-1 / 2, s₂, (-1 / 2) ^ 2 + s₂ ^ 2)} ⊆ {(r, s, t) : ℝ × ℝ × ℝ | r ^ 2 + s ^ 2 = t ∧ r + s + t = k} := by
        intro ⟨r, s, t⟩
        simp
        rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
        . simp
          linarith only [hs₁]
        . simp
          linarith only [hs₂]
      -- So the set has at least two elements, contradicting the assumption that there is exactly one solution.
      have H₂ := Set.encard_mono H₁
      rw [Set.encard_pair (by simp [hs])] at H₂
      rw [H] at H₂
      simp at H₂
