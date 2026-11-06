import Mathlib

open Real Set
open scoped BigOperators

/-
8. Set $A=\{(x, y) \mid y=a x+1, x, y \in \mathbf{R}\}, B=\{(x, y) \mid y=| x |$, $x, y \in \mathbf{R}\}$, and $A \cap B$ is a singleton set, the range of real number $a$ is $\qquad$
-/
theorem algebra_238122 :
   {a : ℝ | ({(x, y) | y = a * x + 1} ∩ {(x, y) | y = |x|}).ncard = 1} = Iic (-1) ∪ Ici 1 := by
  -- 8. $(-\infty,-1] \cup[1,+\infty)$. 在同一坐标系内画出两曲线即可得.
  ext a
  simp
  by_cases ha : a ≤ -1
  · -- Case I : a ≤ -1
    -- We prove that the intersection of these two set is exactly {(1/(1-a), 1/(1-a))}
    simp [ha]
    use (1 / (1 - a)), 1 / (1 - a)
    ext ⟨x, y⟩
    simp
    constructor <;> intro ⟨h₁, h₂⟩
    · -- We solve the equation |x| = ax + 1.
      rw [h₂]
      rw [h₁] at h₂
      by_cases hx : x ≥ 0
      · -- If x ≥ 0, this is equivalent to x = ax+1,
        -- which is impossible.
        rw [abs_of_nonneg hx] at h₂
        have : x = 1 / (1- a) := by
          have : 1 - a > 0 := by linarith only [ha]
          field_simp
          rw [mul_sub, mul_one]
          nth_rw 1 [←h₂]
          ring
        simp only [this, one_div, abs_eq_self, inv_nonneg, sub_nonneg, true_and, ge_iff_le]
        apply le_trans ha
        simp
      · -- If x < 0, then x = 1/(1-a).
        simp at hx
        rw [abs_of_neg hx] at h₂
        have : a * x + 1 > -x := by
          apply sub_pos.mp
          ring_nf
          rw [add_assoc]
          apply add_pos_of_pos_of_nonneg
          · simp
          · trans (a + 1) * x
            · apply mul_nonneg_of_nonpos_of_nonpos
              · linarith only [ha]
              · linarith only [hx]
            · apply le_of_eq
              ring
        simp [h₂] at this
    · -- It is easy to verify that this point belongs to A ∩ B
      rw [h₁, h₂]
      constructor
      · have : 1 - a > 0 := by linarith only [ha]
        field_simp
      · rw [abs_of_nonneg]
        simp only [inv_nonneg, sub_nonneg]
        apply le_trans ha
        simp
  · -- Case II: a ≥ 1
    -- We prove that intersection is {(-1/(a+1),1/(a_1)))}
    by_cases ha' : a ≥ 1
    · simp [ha']
      use -(1 / (a + 1)), 1 / (a + 1)
      ext ⟨x, y⟩
      simp
      constructor <;> intro ⟨h₁, h₂⟩
      · -- Similary, we solve the equation |x|=ax+1
        rw [h₂]
        rw [h₁] at h₂
        by_cases hx : x ≥ 0
        · -- if x≥ 0, then x = -1/(a+1).
          rw [abs_of_nonneg hx] at h₂
          have : a * x + 1 > x := by
            apply sub_pos.mp
            ring_nf
            apply add_pos_of_pos_of_nonneg
            · simp
            · trans (a - 1) * x
              · apply mul_nonneg
                · linarith only [ha']
                · linarith only [hx]
              · apply le_of_eq
                ring
          simp [h₂] at this
        · have : x = -(1 / (a + 1)) := by
            have : a + 1 > 0 := by linarith only [ha']
            field_simp
            rw [mul_add, mul_comm, mul_one]
            rw [abs_of_neg] at h₂
            linarith only [h₂]
            simpa using hx
          simp only [this, one_div, abs_neg, abs_eq_self, inv_nonneg, true_and, ge_iff_le]
          linarith only [ha']
      · --If x < 0, then -x = ax + 1 has no solution since a ≥ 1
        simp [h₁, h₂]
        constructor
        · have : a + 1 > 0 := by linarith only [ha']
          field_simp
        · rw [abs_of_nonneg]
          simp only [inv_nonneg]
          linarith only [ha']
    · -- Case III: -1 < a < 1
      -- The equation has at least two solution (1/(1-a),1/(1-a)) and (-1/(1+a),1/(a+1)).
      -- Hence, it can't be singleton.
      simp [ha, ha']
      simp at ha ha'
      intro x y
      by_contra h
      by_cases hx : x < 0
      · have : (1 / (1 - a), 1 / (1 - a)) ∈ ({(x, y)} : Set <| ℝ × ℝ) := by
          rw [←h]
          simp
          constructor
          · have : 1 - a > 0 := by linarith only [ha']
            field_simp
          · rw [abs_of_nonneg]
            simp
            apply le_of_lt ha'
        simp at this
        obtain h := this.1
        have : x > 0 := by
          rw [←h]
          simp
          exact ha'
        linarith only [hx, this]
      · simp at hx
        rcases lt_or_eq_of_le hx with hx | hx
        · have : (-(1 / (1 + a)), 1 / (1 + a)) ∈ ({(x, y)} : Set <| ℝ × ℝ) := by
            rw [←h]
            simp
            constructor
            · rw [inv_eq_one_div]
              have : 1 + a > 0 := by linarith only [ha]
              field_simp
            · rw [abs_of_nonneg]
              simp
              linarith only [ha]
          simp at this
          obtain h := this.1
          have : x < 0 := by
            rw [←h]
            simp only [Left.neg_neg_iff, inv_pos]
            linarith only [ha]
          linarith only [hx, this]
        · have : (x, y) ∈ ({(x, y)} : Set <| ℝ × ℝ) := by simp
          rw [←h] at this
          simp at this
          simp [←hx] at this
          linarith only [this.1, this.2]
