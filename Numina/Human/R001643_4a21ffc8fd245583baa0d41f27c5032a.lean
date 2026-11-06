import Mathlib

open Real

/-9. (NET 2) $)^{\mathrm{IMO} 4}$ Find all solutions in positive real numbers $x_{i}(i=$ $1,2,3,4,5)$ of the following system of inequalities:
 $$ \begin{aligned} & \left(x_{1}^{2}-x_{3} x_{5}\right)\left(x_{2}^{2}-x_{3} x_{5}\right) \leq 0,\\
  & \left(x_{2}^{2}-x_{4} x_{1}\right)\left(x_{3}^{2}-x_{4} x_{1}\right) \leq 0, \\
  & \left(x_{3}^{2}-x_{5} x_{2}\right)\left(x_{4}^{2}-x_{5} x_{2}\right) \leq 0, \\
  & \left(x_{4}^{2}-x_{1} x_{3}\right)\left(x_{5}^{2}-x_{1} x_{3}\right) \leq 0, \\
  & \left(x_{5}^{2}-x_{2} x_{4}\right)\left(x_{1}^{2}-x_{2} x_{4}\right) \leq 0 . \end{aligned} $$-/
theorem other_24956 :
    {x : Fin 5 → ℝ | (∀ i, 0 < x i) ∧
      (x 0 ^ 2 - x 2 * x 4) * (x 1 ^ 2 - x 2 * x 4) ≤ 0 ∧
      (x 1 ^ 2 - x 3 * x 0) * (x 2 ^ 2 - x 3 * x 0) ≤ 0 ∧
      (x 2 ^ 2 - x 4 * x 1) * (x 3 ^ 2 - x 4 * x 1) ≤ 0 ∧
      (x 3 ^ 2 - x 0 * x 2) * (x 4 ^ 2 - x 0 * x 2) ≤ 0 ∧
      (x 4 ^ 2 - x 1 * x 3) * (x 0 ^ 2 - x 1 * x 3) ≤ 0} =
    {x : Fin 5 → ℝ | ∃ y > 0, ∀ i, x i = y} := by

  -- Clear, x1=x2=x3=x4=x5=y>0 is a solution.
  ext x
  simp
  constructor <;> intro h
  · obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := h
    -- Let L₁ = (x 0 ^ 2 - x 2 * x 4) * (x 1 ^ 2 - x 2 * x 4); L₂ = (x 1 ^ 2 - x 3 * x 0) * (x 2 ^ 2 - x 3 * x 0);
    -- L₃ = (x 2 ^ 2 - x 4 * x 1) * (x 3 ^ 2 - x 4 * x 1); L₄ = (x 3 ^ 2 - x 0 * x 2) * (x 4 ^ 2 - x 0 * x 2);
    -- L₅ = (x 4 ^ 2 - x 1 * x 3) * (x 0 ^ 2 - x 1 * x 3).
    let L (m n p q : Fin 5) := (x m ^ 2 - x p * x q) * (x n ^ 2 - x p * x q)
    -- 0 ≥ L₁ ≥ x 0 ^ 2 * x 1 ^ 2 + x 2 ^ 2 * x 4 ^ 2 - 1 / 2 * (x 0 ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 4 ^ 2)
    -- Similarly for L₂, L₃, L₄, L₅.
    have hL (m n p q : Fin 5) : L m n p q ≥ x m ^ 2 * x n ^ 2 + x p ^ 2 * x q ^ 2 - 1 / 2 * (x m ^ 2 + x n ^ 2) * (x p ^ 2 + x q ^ 2) := by
      unfold L
      trans x m ^ 2 * x n ^ 2 + x p ^ 2 * x q ^ 2 - (x m ^ 2 + x n ^ 2) * (x p * x q)
      · apply le_of_eq
        ring
      · apply sub_le_sub
        · apply le_of_eq
          ring
        · nth_rw 4 [mul_comm]
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left
          · apply sub_nonneg.mp
            trans 1 / 2 * (x p - x q) ^ 2
            · positivity
            · apply le_of_eq
              ring
          · positivity
    -- Therefore, 0 ≥ L₁ + L₂ + L₃ + L₄ + L₅ ≥ 0
    have hsum : L 0 1 2 4 + L 1 2 3 0 + L 2 3 4 1 + L 3 4 0 2 + L 4 0 1 3 = 0 := by
      apply le_antisymm
      · simp [L]
        linarith only [h₁, h₂, h₃, h₄, h₅]
      · trans x 0 ^ 2 * x 1 ^ 2 + x 2 ^ 2 * x 4 ^ 2 - 1 / 2 * (x 0 ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 4 ^ 2) +
          (x 1 ^ 2 * x 2 ^ 2 + x 3 ^ 2 * x 0 ^ 2 - 1 / 2 * (x 1 ^ 2 + x 2 ^ 2) * (x 3 ^ 2 + x 0 ^ 2)) +
          (x 2 ^ 2 * x 3 ^ 2 + x 4 ^ 2 * x 1 ^ 2 - 1 / 2 * (x 2 ^ 2 + x 3 ^ 2) * (x 4 ^ 2 + x 1 ^ 2)) +
          (x 3 ^ 2 * x 4 ^ 2 + x 0 ^ 2 * x 2 ^ 2 - 1 / 2 * (x 3 ^ 2 + x 4 ^ 2) * (x 0 ^ 2 + x 2 ^ 2)) +
          (x 4 ^ 2 * x 0 ^ 2 + x 1 ^ 2 * x 3 ^ 2 - 1 / 2 * (x 4 ^ 2 + x 0 ^ 2) * (x 1 ^ 2 + x 3 ^ 2))
        · apply le_of_eq
          ring
        · gcongr
          all_goals apply hL
    -- We obtain that L₁ = 0, L₂ = 0, L₃ = 0, L₄ = 0, L₅ = 0.
    have h₁ : L 0 1 2 4 = 0 := by
      apply le_antisymm h₁
      by_contra h₁
      simp at h₁
      have : L 0 1 2 4 + L 1 2 3 0 + L 2 3 4 1 + L 3 4 0 2 + L 4 0 1 3 < 0 := by
        simp [L]
        linarith only [h₁, h₂, h₃, h₄, h₅]
      simp [hsum] at this
    simp [h₁] at hsum
    have h₂ : L 1 2 3 0 = 0 := by
      apply le_antisymm h₂
      by_contra h₂
      simp at h₂
      have : L 1 2 3 0 + L 2 3 4 1 + L 3 4 0 2 + L 4 0 1 3 < 0 := by
        simp [L]
        linarith only [h₂, h₃, h₄, h₅]
      simp [hsum] at this
    simp [h₂] at hsum
    have h₃ : L 2 3 4 1 = 0 := by
      apply le_antisymm h₃
      by_contra h₃
      simp at h₃
      have : L 2 3 4 1 + L 3 4 0 2 + L 4 0 1 3 < 0 := by
        simp [L]
        linarith only [h₃, h₄, h₅]
      simp [hsum] at this
    simp [h₃] at hsum
    have h₄ : L 3 4 0 2 = 0 := by
      apply le_antisymm h₄
      by_contra h₄
      simp at h₄
      have : L 3 4 0 2 + L 4 0 1 3 < 0 := by
        simp [L]
        linarith only [h₄, h₅]
      simp [hsum] at this
    simp [h₄] at hsum
    have h₅ : L 4 0 1 3 = 0 := hsum
    simp [L] at h₁ h₂ h₃ h₄ h₅
    -- Then x 0 ^ 2 = x 2 * x 4 or x 1 ^ 2 = x 2 * x 4, ...
    -- In all these cases, we can prove that x 0 = x 1 = x 2 = x 3 = x 4.
    rcases h₁ with h₁ | h₁
    · have h₁ : x 0 ^ 2 = x 2 * x 4 := by
        apply sub_eq_zero.mp h₁
      rcases h₂ with h₂ | h₂
      · have h₂ : x 1 ^ 4 = x 3 ^ 2 * x 2 * x 4 := by
          apply sub_eq_zero.mp at h₂
          rw [mul_assoc, ←h₁, ←mul_pow, ←h₂]
          ring
        rcases h₃ with h₃ | h₃
        · have h₃ : x 2 ^ 7 = x 4 ^ 5 * x 3 ^ 2 := by
            suffices h : x 2 * x 2 ^ 7 = x 2 * (x 4 ^ 5 * x 3 ^ 2)
            · apply mul_right_injective₀ ?_ h
              apply ne_of_gt
              apply h₀
            · apply sub_eq_zero.mp at h₃
              trans (x 2 ^ 2) ^ 4
              · ring
              · rw [h₃, mul_pow, h₂]
                ring
          rcases h₄ with h₄ | h₄
          · have h₄ : x 3 ^ 12 = x 0 ^ 7 * x 4 ^ 5 := by
              suffices h : x 3 ^ 2 * x 3 ^ 12 = x 3 ^ 2 * (x 0 ^ 7 * x 4 ^ 5)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply sq_pos_of_pos
                apply h₀
              · apply sub_eq_zero.mp at h₄
                trans (x 3 ^ 2) ^ 7
                · ring
                · nth_rw 1 [h₄, mul_pow, h₃]
                  ring
            have h₄ : x 3 ^ 24 = x 4 ^ 5 * x 3 ^ 2 * x 4 ^ 7 * x 4 ^ 10 := by
              rw [←h₃, ←mul_pow, ←h₁, ←pow_mul]
              norm_num
              trans (x 3 ^ 12) ^ 2
              · ring
              · rw [h₄]
                ring
            have h₄ : x 3 ^ 22 = x 4 ^ 22 := by
              suffices h : x 3 ^ 2 * x 3 ^ 22 = x 3 ^ 2 * (x 4 ^ 22)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply sq_pos_of_pos
                apply h₀
              · trans x 3 ^ 24
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 3 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 2 ^ 7 = x 4 ^ 7 := by
              rw [h₃, h₄]
              ring
            have h₃ : x 2 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₂ : x 1 ^ 4 = x 4 ^ 4 := by
              rw [h₂, h₃, h₄]
              ring
            have h₂ : x 1 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₁ : x 0 ^ 2 = x 4 ^ 2 := by
              rw [h₁, h₃]
              ring
            have h₁ : x 0 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · have h₄ : x 4 ^ 9 = x 0 ^ 7 * x 3 ^ 2 := by
              suffices h : x 4 ^ 5 * x 4 ^ 9 = x 4 ^ 5 * (x 0 ^ 7 * x 3 ^ 2)
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              · apply sub_eq_zero.mp at h₄
                trans (x 4 ^ 2) ^ 7
                · ring
                · rw [h₄, mul_pow, h₃]
                  ring
            have h₄ : x 4 ^ 18 = (x 2 * x 4) ^ 7 * x 3 ^ 4 := by
              trans (x 4 ^ 9) ^ 2
              · ring
              · rw [h₄, mul_pow, ←h₁]
                ring
            rw [mul_pow, h₃] at h₄
            have h₄ : x 4 ^ 6 = x 3 ^ 6 := by
              suffices h : x 4 ^ 12 * x 4 ^ 6 = x 4 ^ 12 * (x 3 ^ 6)
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              · trans x 4 ^ 18
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 4 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 2 ^ 7 = x 3 ^ 7 := by
              rw [h₃, h₄]
              ring
            have h₃ : x 2 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₂ : x 1 ^ 4 = x 3 ^ 4 := by
              rw [h₂, h₃, h₄]
              ring
            have h₂ : x 1 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₁ : x 0 ^ 2 = x 3 ^ 2 := by
              rw [h₁, h₃, h₄]
              ring
            have h₁ : x 0 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 3
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
        · apply sub_eq_zero.mp at h₃
          rw [h₃] at h₂
          have h₂ : x 1 ^ 3 = x 2 * x 4 ^ 2 := by
            suffices h : x 1 * x 1 ^ 3 = x 1 * (x 2 * x 4 ^ 2)
            · apply mul_right_injective₀ ?_ h
              apply ne_of_gt
              apply h₀
            · trans x 1 ^ 4
              · ring
              · rw [h₂]
                ring
          rcases h₄ with h₄ | h₄
          · have h₄ : x 3 ^ 4 = x 4 * x 2 ^ 3 := by
              trans (x 3 ^ 2) ^ 2
              · ring
              · apply sub_eq_zero.mp at h₄
                rw [h₄, mul_pow, h₁]
                ring
            have h₄ : (x 4 ^ 3 * (x 2 * x 4 ^ 2)) ^ 2 = (x 4 * x 2 ^ 3) ^ 3 := by
              rw [←h₄, ←h₂]
              trans (x 3 ^ 2) ^ 6
              · rw [h₃]
                ring
              · ring
            have h₄ : x 4 ^ 7 = x 2 ^ 7 := by
              suffices h : x 4 ^ 3 * x 4 ^ 7 = x 4 ^ 3 * (x 2 ^ 7)
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              suffices h : x 2 ^ 2 * (x 4 ^ 3 * x 4 ^ 7) = x 2 ^ 2 * (x 4 ^ 3 * (x 2 ^ 7))
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              · trans (x 4 ^ 3 * (x 2 * x 4 ^ 2)) ^ 2
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 4 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₁ h₂ h₃
            have h₁ : x 0 ^ 2 = x 2 ^ 2 := by rw [h₁]; ring
            have h₁ : x 0 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₂ : x 1 ^ 3 = x 2 ^ 3 := by rw [h₂]; ring
            have h₂ : x 1 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₂] at h₃
            have h₃ : x 3 ^ 2 = x 2 ^ 2 := by rw [h₃]; ring
            have h₃ : x 3 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 2
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · have h₄ : x 4 ^ 4 = x 2 * x 4 * x 2 ^ 2 := by
              rw [←h₁, ←mul_pow]
              apply sub_eq_zero.mp at h₄
              rw [←h₄]
              ring
            have h₄ : x 4 ^ 3 = x 2 ^ 3 := by
              suffices h : x 4 * x 4 ^ 3 = x 4 * (x 2 ^ 3)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans x 4 ^ 4
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 4 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₁ h₂ h₃
            have : x 0 ^ 2 = x 2 ^ 2 := by rw [h₁]; ring
            have h₁ : x 0 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp this
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₂ : x 1 ^ 3 = x 2 ^ 3 := by rw [h₂]; ring
            have h₂ : x 1 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₂] at h₃
            have h₃ : x 3 ^ 2 = x 2 ^ 2 := by rw [h₃]; ring
            have h₃ : x 3 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 2
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
      · have h₂ : x 2 ^ 3 = x 3 ^ 2 * x 4 := by
          suffices h : x 2 * x 2 ^ 3 = x 2 * (x 3 ^ 2 * x 4)
          · apply mul_right_injective₀ ?_ h
            apply ne_of_gt
            apply h₀
          · trans (x 2 ^ 2) ^ 2
            · ring
            · apply sub_eq_zero.mp at h₂
              rw [h₂, mul_pow, h₁]
              ring
        have h₁ : x 0 ^ 6 = x 3 ^ 2 * x 4 ^ 4 := by
          trans (x 0 ^ 2) ^ 3
          · ring
          · rw [h₁, mul_pow, h₂]
            ring
        rcases h₃ with h₃ | h₃
        · apply sub_eq_zero.mp at h₃
          rcases h₄ with h₄ | h₄
          · apply sub_eq_zero.mp at h₄
            rw [h₄] at h₁ h₂
            have h₂ : x 2 ^ 2 = x 0 * x 4 := by
              suffices h : x 2 * x 2 ^ 2 = x 2 * (x 0 * x 4)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans x 2 ^ 3
                · ring
                · rw [h₂]
                  ring
            have h₁ : x 0 ^ 5 = x 2 * x 4 ^ 4 := by
              suffices h : x 0 * x 0 ^ 5 = x 0 * (x 2 * x 4 ^ 4)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans x 0 ^ 6
                · ring
                · rw [h₁]
                  ring
            have h₁ : x 0 ^ 9 = x 4 ^ 9 := by
              suffices h : x 0 * x 0 ^ 9 = x 0 * (x 4 ^ 9)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans (x 0 ^ 5) ^ 2
                · ring
                · rw [h₁, mul_pow, h₂]
                  ring
            have h₁ : x 0 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₁] at h₂ h₄
            have h₂ : x 2 ^ 2 = x 4 ^ 2 := by rw [h₂]; ring
            have h₂ : x 2 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₂] at h₃ h₄
            have h₄ : x 3 ^ 2 = x 4 ^ 2 := by rw [h₄]; ring
            have h₄ : x 3 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 4 = x 1 := by
              rw [sq] at h₃
              apply mul_right_injective₀ ?_ h₃
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₃
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            have h₄ : x 4 ^ 12 = x 0 ^ 6 * (x 2 ^ 3) ^ 2 := by
              trans (x 4 ^ 2) ^ 6
              · ring
              · rw [h₄]
                ring
            rw [h₁, h₂] at h₄
            have h₄ : x 4 ^ 6 = x 3 ^ 6 := by
              suffices h : x 4 ^ 6 * x 4 ^ 6 = x 4 ^ 6 * (x 3 ^ 6)
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              · trans x 4 ^ 12
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 4 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₁ h₂ h₃
            have h₂ : x 2 ^ 3 = x 3 ^ 3 := by rw [h₂]; ring
            have h₂ : x 2 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₂] at h₃
            have h₁ : x 0 ^ 6 = x 3 ^ 6 := by rw [h₁]; ring
            have h₁ : x 0 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 3 = x 1 := by
              rw [sq] at h₃
              apply mul_right_injective₀ ?_ h₃
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₃
            use x 3
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
        · apply sub_eq_zero.mp at h₃
          rw [h₃] at h₁ h₂
          rcases h₄ with h₄ | h₄
          · rw [h₃] at h₄
            apply sub_eq_zero.mp at h₄
            have h₄ : x 4 ^ 6 * x 1 ^ 6 = x 0 ^ 6 * (x 2 ^ 3) ^ 2 := by
              trans (x 4 * x 1) ^ 6
              · ring
              · rw [h₄]
                ring
            rw [h₁, h₂] at h₄
            have h₄ : x 1 ^ 3 = x 4 ^ 3 := by
              suffices h : x 4 ^ 6 * x 1 ^ 3 * x 1 ^ 3 = x 4 ^ 6 * x 1 ^ 3 * (x 4 ^ 3)
              · apply mul_right_injective₀ ?_ h
                simp
                constructor
                all_goals
                  apply ne_of_gt
                  apply h₀
              · trans x 4 ^ 6 * x 1 ^ 6
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 1 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₁ h₂ h₃
            have h₂ : x 2 ^ 3 = x 4 ^ 3 := by rw [h₂]; ring
            have h₂ : x 2 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₁ : x 0 ^ 6 = x 4 ^ 6 := by rw [h₁]; ring
            have h₁ : x 0 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 3 ^ 2 = x 4 ^ 2 := by rw [h₃]; ring
            have h₃ : x 3 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            have h₄ : x 4 ^ 12 = x 0 ^ 6 * (x 2 ^ 3) ^ 2 := by
              trans (x 4 ^ 2) ^ 6
              · ring
              · rw [h₄]
                ring
            rw [h₁, h₂] at h₄
            have h₄ : x 4 ^ 3 = x 1 ^ 3 := by
              suffices h : x 4 ^ 9 * x 4 ^ 3 = x 4 ^ 9 * (x 1 ^ 3)
              · apply mul_right_injective₀ ?_ h
                simp
                apply ne_of_gt
                apply h₀
              · trans x 4 ^ 12
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 4 = x 1 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₁ h₂ h₃
            have h₂ : x 2 ^ 3 = x 1 ^ 3 := by rw [h₂]; ring
            have h₂ : x 2 = x 1 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₃ : x 3 ^ 2 = x 1 ^ 2 := by rw [h₃]; ring
            have h₃ : x 3 = x 1 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            have h₁ : x 0 ^ 6 = x 1 ^ 6 := by rw [h₁]; ring
            have h₁ : x 0 = x 1 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 1
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
    · apply sub_eq_zero.mp at h₁
      rcases h₂ with h₂ | h₂
      · apply sub_eq_zero.mp at h₂
        rcases h₃ with h₃ | h₃
        · apply sub_eq_zero.mp at h₃
          have h₃ : x 2 ^ 3 = x 4 ^ 3 := by
            suffices h : x 2 * x 2 ^ 3 = x 2 * x 4 ^ 3
            · apply mul_right_injective₀ ?_ h
              apply ne_of_gt
              apply h₀
            · trans (x 2 ^ 2) ^ 2
              · ring
              · rw [h₃, mul_pow, h₁]
                ring
          have h₃ : x 2 = x 4 := by
            apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
            · apply le_of_lt
              apply h₀
            · apply le_of_lt
              apply h₀
            · simp
          rw [h₃] at h₁ h₄
          have h₁ : x 1 ^ 2 = x 4 ^ 2 := by rw [h₁]; ring
          have h₁ : x 1 = x 4 := by
            apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
            · apply le_of_lt
              apply h₀
            · apply le_of_lt
              apply h₀
            · simp
          rw [h₁] at h₂
          rcases h₄ with h₄ | h₄
          · apply sub_eq_zero.mp at h₄
            have h₄ : x 3 ^ 4 = x 0 ^ 2 * x 3 * x 0 := by
              trans (x 3 ^ 2) ^ 2
              · ring
              · rw [h₄, mul_pow, h₂]
                ring
            have h₄ : x 3 ^ 3 = x 0 ^ 3 := by
              suffices h : x 3 * x 3 ^ 3 = x 3 * (x 0 ^ 3)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans x 3 ^ 4
                · ring
                · rw [h₄]
                  ring
            have h₄ : x 3 = x 0 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₂
            have h₂ : x 4 ^ 2 = x 0 ^ 2 := by rw [h₂]; ring
            have h₂ : x 4 = x 0 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₂
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₂] at h₃ h₁
            use x 0
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            rw [sq] at h₄
            have h₄ : x 4 = x 0 := by
              apply mul_left_injective₀ ?_ h₄
              apply ne_of_gt
              apply h₀
            rw [h₄] at h₁ h₂ h₃
            rw [sq] at h₂
            have h₂ : x 0 = x 3 := by
              apply mul_left_injective₀ ?_ h₂
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₂
            use x 0
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
        · apply sub_eq_zero.mp at h₃
          have h₃ : x 3 ^ 4 = x 4 ^ 2 * x 3 * x 0 := by
            trans (x 3 ^ 2) ^ 2
            · ring
            · rw [h₃, mul_pow, h₂]
              ring
          rcases h₄ with h₄ | h₄
          · apply sub_eq_zero.mp at h₄
            rw [h₁] at h₂
            have h₄ : x 3 ^ 2 * x 4 = x 0 * (x 2 * x 4) := by
              rw [←mul_assoc]
              congr
            rw [h₂] at  h₄
            have h₄ : x 3 = x 0 ^ 2 / x 4 := by
              have : x 4 > 0 := by apply h₀
              field_simp
              suffices h : x 3 * (x 3 * x 4) = x 3 * (x 0 ^ 2)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · trans x 3 ^ 2 * x 4
                · ring
                · rw [h₄]
                  ring
            rw [h₄] at h₃
            have : x 4 > 0 := by apply h₀
            field_simp at h₃
            have h₃ : x 0 ^ 5 = x 4 ^ 5 := by
              suffices h : x 0 ^ 3 * x 4 * (x 0 ^ 5) = x 0 ^ 3 * x 4 * (x 4 ^ 5)
              · apply mul_right_injective₀ ?_ h
                simp
                constructor
                all_goals
                  apply ne_of_gt
                  apply h₀
              · apply Eq.trans ?_ (Eq.trans h₃ ?_)
                all_goals ring
            have h₃ : x 0 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₃] at h₂ h₄
            field_simp at h₄
            have h₄ : x 3 = x 4 := by
              rw [sq] at h₄
              apply mul_left_injective₀ ?_ h₄
              apply ne_of_gt
              apply h₀
            rw [h₄] at h₂
            have h₂ : x 2 = x 4 := by
              apply mul_left_injective₀ ?_ h₂
              apply ne_of_gt
              apply h₀
            rw [h₂] at h₁
            rw [←sq] at h₁
            have h₁ : x 1 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            rw [h₁] at h₂
            have : x 2 > 0 := by apply h₀
            have h₄ : x 0 = x 4 ^ 2 / x 2 := by
              field_simp
              rw [h₄]
            rw [h₄] at h₂ h₃
            field_simp at h₂ h₃
            have : x 4 > 0 := by apply h₀
            have h₂ : x 3 = (x 2 ^ 2 * x 4) / x 4 ^ 2 := by
              field_simp
              rw [←h₂]
              ring
            rw [h₂] at h₃
            field_simp at h₃
            ring_nf at h₃
            apply sub_eq_zero.mpr at h₃
            have h₃ : x 2 ^ 2 * x 4 ^ 4 * (x 2 ^ 7 - x 4 ^ 7) = 0 := by
              rw [←h₃]
              ring
            simp at h₃
            have : x 2 ≠ 0 := by
              apply ne_of_gt
              apply h₀
            simp [this] at h₃
            have : x 4 ≠ 0 := by
              apply ne_of_gt
              apply h₀
            simp [this] at h₃
            apply sub_eq_zero.mp at h₃
            have h₃ : x 2 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₃] at h₁ h₂ h₄
            rw [sq] at h₄ h₂
            field_simp at h₄ h₂
            have h₁ : x 1 = x 4 := by
              rw [←sq] at h₁
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
      · apply sub_eq_zero.mp at h₂
        rcases h₃ with h₃ | h₃
        · apply sub_eq_zero.mp at h₃
          have h₃ : x 2 ^ 4 = x 4 ^ 2 * x 2 * x 4 := by
            trans (x 2 ^ 2) ^ 2
            · ring
            · rw [h₃, mul_pow, h₁]
              ring
          have h₃ : x 2 ^ 3 = x 4 ^ 3 := by
            suffices h : x 2 * x 2 ^ 3 = x 2 * (x 4 ^ 3)
            · apply mul_right_injective₀ ?_ h
              apply ne_of_gt
              apply h₀
            · trans x 2 ^ 4
              · ring
              · rw [h₃]
                ring
          have h₃ : x 2 = x 4 := by
            apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
            · apply le_of_lt
              apply h₀
            · apply le_of_lt
              apply h₀
            · simp
          rw [h₃] at h₁ h₂
          rw [←sq] at h₁
          have h₁ : x 1 = x 4 := by
            apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
            · apply le_of_lt
              apply h₀
            · apply le_of_lt
              apply h₀
            · simp
          rw [h₃] at h₄
          rcases h₄ with h₄ | h₄
          · apply sub_eq_zero.mp at h₄
            have h₄ : x 0 * x 4 * x 4 ^ 2 = x 3 ^ 2 * x 3 * x 0 := by
              rw [h₂, ←h₄]
              ring
            have h₄ : x 4 ^ 3 = x 3 ^ 3 := by
              suffices h : x 0 * x 4 ^ 3 = x 0 * (x 3 ^ 3)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · apply Eq.trans ?_ (Eq.trans h₄ ?_)
                all_goals ring
            have h₄ : x 4 = x 3 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [eq_comm] at h₄
            rw [h₄, sq] at h₂
            have h₂ : x 4 = x 0 := by
              apply mul_right_injective₀ ?_ h₂
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₂
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            rw [sq] at h₄
            have h₄ : x 4 = x 0 := by
              apply mul_left_injective₀ ?_ h₄
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₄
            rw [h₄] at h₂
            rw [sq] at h₂
            have h₂ : x 4 = x 3 := by
              apply mul_left_injective₀ ?_ h₂
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₂
            use x 4
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
        · apply sub_eq_zero.mp at h₃
          rcases h₄ with h₄ | h₄
          · apply sub_eq_zero.mp at h₄
            have h₄ : x 3 * x 3 ^ 2 = x 2 ^ 2 * x 2 := by
              rw [h₄, h₂]
              ring
            have h₄ : x 3 ^ 3 = x 2 ^ 3 := by
              apply Eq.trans ?_ (Eq.trans h₄ ?_)
              all_goals ring
            have h₄ : x 3 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [h₄] at h₂ h₃
            rw [sq] at h₂
            have h₂ : x 2 = x 0 := by
              apply mul_right_injective₀ ?_ h₂
              apply ne_of_gt
              apply h₀
            rw [eq_comm] at h₂
            have h₃ : x 2 ^ 4 = x 4 ^ 2 * x 2 * x 4 := by
              trans (x 2 ^ 2) ^ 2
              · ring
              · rw [h₃, mul_pow, h₁]
                ring
            have h₃ : x 2 ^ 3 = x 4 ^ 3 := by
              suffices h : x 2 * x 2 ^ 3 = x 2 * (x 4 ^ 3)
              · apply mul_right_injective₀ ?_ h
                apply ne_of_gt
                apply h₀
              · apply Eq.trans ?_ (Eq.trans h₃ ?_)
                all_goals ring
            have h₃ : x 2 = x 4 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₃
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            rw [eq_comm] at h₃
            rw [h₃] at h₁
            rw [←sq] at h₁
            have h₁ : x 1 = x 2 := by
              apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₁
              · apply le_of_lt
                apply h₀
              · apply le_of_lt
                apply h₀
              · simp
            use x 2
            constructor
            · apply h₀
            · intro i
              fin_cases i
              all_goals simp
              all_goals assumption
          · apply sub_eq_zero.mp at h₄
            have h₁ : x 4 = x 1 ^ 2 / x 2 := by
              have : x 2 > 0 := by apply h₀
              field_simp
              rw [h₁]
              ring
            rw [h₁] at h₃ h₄
            have : x 2 > 0 := by apply h₀
            field_simp at h₃ h₄
            have : x 3 > 0 := by apply h₀
            have h₂ : x 0 = x 2 ^ 2 / x 3 := by
              field_simp
              rw [h₂]
              ring
            rw [h₂] at h₄
            field_simp at h₄
            have h₃ : x 2 = x 1 ^ 3 / x 3 ^ 2 := by
              field_simp
              apply Eq.trans ?_ (Eq.trans h₃ ?_)
              all_goals ring
            rw [h₃] at h₄
            field_simp at h₄
            apply sub_eq_zero.mpr at h₄
            ring_nf at h₄
            have h₄ : x 1 ^ 4 * (x 3 ^ 11 - x 1 ^ 11) = 0 := by
              rw [←h₄]
              ring
            simp at h₄
            rcases h₄ with h₄ | h₄
            · have h₄ : x 1 ≠ 0 := by
                apply ne_of_gt
                apply h₀
              contradiction
            · apply sub_eq_zero.mp at h₄
              have h₄ : x 3 = x 1 := by
                apply pow_left_inj₀ ?_ ?_ ?_ |>.mp h₄
                · apply le_of_lt
                  apply h₀
                · apply le_of_lt
                  apply h₀
                · simp
              rw [h₄] at h₂ h₃
              rw [show (3 : ℕ) = 1 + 2 by simp, pow_add] at h₃
              have : x 1 > 0 := by apply h₀
              field_simp at h₃
              rw [h₃] at h₁ h₂
              rw [sq] at h₁ h₂
              field_simp at h₁ h₂
              use x 1
              constructor
              · apply h₀
              · intro i
                fin_cases i
                all_goals simp
                all_goals assumption
  · obtain ⟨y, hy, hx⟩ := h
    simp [hx]
    constructor
    · exact hy
    · apply le_of_eq
      ring
