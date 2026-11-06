import Mathlib

/- For which non-negative values of the parameter $a$ does the equation

 abs ((x^3 - 10 * x^2 + 31 * x - 30) / (x^2 - 8 * x + 15)) = (Real.sqrt (2 * x - a))^2 + 2 - 2 * x)

 have one solution? -/
theorem algebra_228191 (a : ℝ) (ha : 0 ≤ a) :
    (∃! x : ℝ, x^2 - 8 * x + 15 ≠ 0 ∧ 0 ≤ 2 * x - a ∧ abs ((x^3 - 10 * x^2 + 31 * x - 30) / (x^2 - 8 * x + 15)) =
      (Real.sqrt (2 * x - a))^2 + 2 - 2 * x) ↔ a = 1 ∨ a = 2 := by

      -- we simplify the equation firstly
      have l: ∀ x: ℝ,  x ^ 2 - 8 * x + 15 ≠ 0 → (x ^ 3 - 10 * x ^ 2 + 31 * x - 30) / (x ^ 2 - 8 * x + 15) = x - 2 := by
          intro x hx
          field_simp
          ring
      have r: ∀ x: ℝ, 0 ≤ 2 * x - a → (Real.sqrt (2 * x - a))^2 + 2 - 2 * x = 2 - a := by
          intro x hx2
          have o: (Real.sqrt (2 * x - a))^2 = 2 * x - a := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            exact hx2
            apply Real.sqrt_nonneg
          rw [o]
          ring
      constructor

      -- forward direction
      .
        intro h
        obtain ⟨x,hx⟩ := h
        rcases hx with ⟨hx,hy⟩
        rcases hx with ⟨hx1,hx2,h⟩

        -- we simplify the equation
        rw [l,r] at h
        have ra: 0 ≤ 2 - a := by  -- prove a < 2
          rw [← h]
          simp
        replace ra: a ≤ 2 := by
          linarith
        by_contra! la
        rcases la with ⟨la,g⟩
        replace ra: a < 2 := by
          by_contra! no
          replace no: a = 2 := by
            linarith
          tauto
        clear g

        -- we note that x = a and x = 4 - a are solutions
        have h1:= hy a   -- use a to show that x = a
        simp at h1
        have f1: a = x := by -- show that a is a solution, so x = a
          clear * - h1 l r ra ha la
          specialize l a
          clear r
          have o1: a ^ 2 - 8 * a + 15 ≠ 0 := by
            nlinarith
          simp [o1] at l
          replace o1: ¬ a ^ 2 - 8 * a + 15 = 0 := by simp [o1]
          simp [o1] at h1
          have o2: 0 ≤ 2 * a - a := by
            nlinarith
          simp [o2] at h1
          have o3: a ≤ 2 * a := by
            nlinarith
          simp [o3] at h1
          rw [l] at h1
          ring_nf at h1
          have o4: |- 2 + a| = - (-2 + a) := by
            apply abs_of_neg
            linarith
          rw [o4] at h1
          ring_nf at h1
          simp at h1
          exact h1
        clear hx1 hx2 h1
        have h2:= hy (4 - a)   -- use 4 - a to show that x = 4 - a
        simp at h2
        have f2: 4 - a = x := by  --show that 4 - a is a solution, so x = 4 - a
          clear * - h2 l r ra ha la
          specialize l (4 - a)
          clear r
          have o1: (4 - a) ^ 2 - 8 * (4 - a) + 15 ≠ 0 := by
            by_contra! no
            rw [show (4 - a) ^ 2 - 8 * (4 - a) + 15 = (a - 1) * (a + 1) by ring] at no
            simp at no
            rcases no with o | o
            . replace o: a = 1 := by
                linarith
              tauto
            . replace o: a = -1 := by
                linarith
              nlinarith
          simp [o1] at l
          replace o1: ¬ (4 - a) ^ 2 - 8 * (4 - a) + 15 = 0 := by simp [o1]
          simp [o1] at h2
          have o2: a ≤ 2 * (4 - a) := by
            nlinarith
          simp [o2] at h2
          have o3: 8 - 3 * a ≤ 8 := by
            nlinarith
          rw [l] at h2
          ring_nf at h2
          have o4: |2 - a| = 2 - a := by
            apply abs_of_pos
            linarith
          rw [o4] at h2
          simp at h2
          exact h2
        nlinarith -- now use f1 and f2, we see that a = 2
        exact hx2
        exact hx1

      -- backward direction
      .
        intro h
        rcases h with h | h
        all_goals simp only [h] at *; clear ha

        -- case 1: a = 1
        . use 1
          constructor
          . simp
            norm_num
          . simp
            intro y hy1 hy2 h
            specialize l y
            simp [hy1] at l
            rw [l] at h
            have lr: √(2 * y - 1) ^ 2 = 2 * y - 1 := by
              symm
              rw [← Real.sqrt_eq_iff_eq_sq]
              nlinarith
              apply Real.sqrt_nonneg
            rw [lr] at h
            ring_nf at h
            have s:= abs_choice (- 2 + y)
            rcases s with s | s
            . rw [s] at h
              replace h: y = 3 := by linarith
              simp [h] at hy1
              norm_num at hy1
            . rw [s] at h
              nlinarith

        -- case 2: a = 2
        . use 2
          constructor
          . simp
            norm_num
          . simp
            intro y hy1 hy2 h
            specialize l y
            simp [hy1] at l
            rw [l] at h
            have lr: √(2 * y - 2) ^ 2 = 2 * y - 2 := by
              symm
              rw [← Real.sqrt_eq_iff_eq_sq]
              nlinarith
              apply Real.sqrt_nonneg
            rw [lr] at h
            ring_nf at h
            have s:= abs_choice (- 2 + y)
            rcases s with s | s
            all_goals rw [s] at h; linarith
    