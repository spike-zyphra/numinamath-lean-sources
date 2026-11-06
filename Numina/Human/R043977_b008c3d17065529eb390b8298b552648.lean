import Mathlib

/-Find all irrational numbers x such that x^3-17x and x^2+4x are both rational numbers -/
theorem algebra_608842: {x: ℝ | (Irrational x)  ∧ (∃ p q: ℚ, x ^ 3 - 17 * x = (p: ℝ) ∧ x ^ 2 + 4 * x = (q: ℝ))}
= {-2 + √5, -2 - √5} := by
    ext x
    have sq_5: √5 ^ 2 = 5 := by   -- Firstly compute √5 ^ 2 --
              symm
              rw [← Real.sqrt_eq_iff_eq_sq]
              norm_num
              norm_num
    have eq1: √5 ^ 3 = √5 * 5 := by  -- Then compute √5 ^ 3 --
              rw [show √5 ^ 3 = √5 * (√5 ^ 2) by ring]
              rw [sq_5]
    constructor

    -- the forward direction --

    . intro h
      simp at h
      simp
      rcases h with ⟨irr_x, h1, h2⟩
      obtain ⟨p, hp⟩ := h1
      obtain ⟨q, hq⟩ := h2
      have h: (x + 2) ^ 2 = q + 4 := by
        ring_nf
        nlinarith [hp]
      let y:= q + 4
      have hy: (q: ℝ) + 4 = (y: ℝ) := by
        simp [y]
      rw [hy] at h
      clear hy hq
      clear_value y
      have y_pos: 0 ≤ (y: ℝ) := by
        rw [← h]
        nlinarith
      by_cases b: 0 ≤ x + 2

      -- for the cases 0 ≤ x + 2 - -
      . symm at h
        rw [← Real.sqrt_eq_iff_eq_sq] at h
        left
        replace h: x = -2 + Real.sqrt y := by
          rw [h]
          ring_nf
        simp [h] at hp
        ring_nf at hp
        have eq_y: √↑y ^ 2 = (y: ℝ)  := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          simp
          simp at y_pos
          exact y_pos
          simp
        rw [eq_y] at hp
        have eq_y2: √↑y ^ 3 = √↑y ^ 2 * √↑y := by ring
        rw [eq_y2] at hp
        rw [eq_y] at hp
        replace hp: (y - 5) * √↑y = ↑p + 6 * ↑y - 26 := by
          nlinarith [hp]
        let r:= p + 6 * y - 26
        have hr: p + 6 * y - 26 = r := by rfl
        rw [show (p: ℝ) + 6 * ↑y - 26 = ↑r by simp [r]] at hp
        clear_value r
        clear hr
        -- now we must have y - 5 = 0 --
        have y_val: y = 5 := by
          by_contra! ne
          let s:= r / (y - 5)
          replace hp: √↑y = ↑s := by
            simp [s]
            rw [eq_div_iff_mul_eq]
            rw [← hp]
            ring
            by_contra! no
            replace no: (y: ℝ)  = 5 := by
              nlinarith
            norm_cast at no
          rw [hp] at h
          rw [show -2 + (s: ℝ) = ↑(-2 + s) by simp] at h
          have contra:= Rat.not_irrational (-2 + s)
          rw [← h] at contra
          tauto
        rw [y_val] at h
        exact h
        simp
        simp at y_pos
        exact y_pos
        exact b

      -- for the cases 0 > x + 2, similar as above --
      . simp at b
        symm at h
        rw [show (x + 2)^2 = (-x-2)^2 by ring] at h
        rw [← Real.sqrt_eq_iff_eq_sq] at h
        right
        replace h: x = -2 - Real.sqrt y := by
          rw [h]
          ring_nf
        simp [h] at hp
        ring_nf at hp
        have eq_y: √↑y ^ 2 = (y: ℝ)  := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          simp
          simp at y_pos
          exact y_pos
          simp
        rw [eq_y] at hp
        have eq_y2: √↑y ^ 3 = √↑y ^ 2 * √↑y := by ring
        rw [eq_y2] at hp
        rw [eq_y] at hp
        replace hp: (y - 5) * √↑y = 26 - 6 * ↑y - ↑p := by
          nlinarith [hp]
        let r:= 26 - 6 * y - p
        have hr: 26 - 6 * y - p = r := by rfl
        rw [show 26 - 6 * (y: ℝ)  - (p: ℝ) = ↑r by simp [r]] at hp
        clear_value r
        clear hr
        -- now we must have y - 5 = 0 --
        have y_val: y = 5 := by
          by_contra! ne
          let s:= r / (y - 5)
          replace hp: √↑y = ↑s := by
            simp [s]
            rw [eq_div_iff_mul_eq]
            rw [← hp]
            ring
            by_contra! no
            replace no: (y: ℝ)  = 5 := by
              nlinarith
            norm_cast at no
          rw [hp] at h
          rw [show -2 - (s: ℝ) = ↑(-2 - s) by simp] at h
          have contra:= Rat.not_irrational (-2 - s)
          rw [← h] at contra
          tauto
        rw [y_val] at h
        exact h
        simp
        simp at y_pos
        exact y_pos
        linarith

    -- the backward direction --
    . intro h
      simp at h
      simp
      rcases h with h | h
      . constructor
        . have l: Irrational √5 := by
            apply Nat.Prime.irrational_sqrt
            norm_num
          have o:= Irrational.rat_add (-2: ℚ) l
          rw [show ((-2: ℚ): ℝ)  = -2 by simp] at o
          rw [h]
          exact o
        . constructor
          . use (-4: ℚ)
            rw [h]
            ring_nf
            rw [eq1]
            ring_nf
            rw [sq_5]
            norm_num
          . use (1: ℚ)
            rw [h]
            ring_nf
            norm_num
      . constructor
        . have l: Irrational √5 := by
            apply Nat.Prime.irrational_sqrt
            norm_num
          have o:= Irrational.rat_sub (-2: ℚ) l
          rw [show ((-2: ℚ): ℝ)  = -2 by simp] at o
          rw [h]
          exact o
        . constructor
          . use (-4: ℚ)
            rw [h]
            ring_nf
            rw [eq1]
            ring_nf
            rw [sq_5]
            norm_num
          . use (1: ℚ)
            rw [h]
            ring_nf
            norm_num