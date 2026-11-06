import Mathlib

/-It's known that a real number a makes the inequality |x ^ 2 + 2 * a * x + 3 * a| ≤ 2
true only for one real number x. Then the number of all real number a satisfy the condition is ?-/

theorem inequalities_621169: {a: ℝ | ∃! x, |x ^ 2 + 2 * a * x + 3 * a| ≤ 2}.encard = 2 := by

    -- we show that a = 1 or 2
    have h_eq: {a: ℝ | ∃! x, |x ^ 2 + 2 * a * x + 3 * a| ≤ 2} = {1, 2} := by
        ext a
        simp
        constructor

        -- the foward direction
        .
            intro h
            obtain ⟨x, hx, hy⟩ := h
            rw [show x ^ 2 + 2 * a * x + 3 * a = (x + a) ^ 2 + 3 * a - a ^ 2 by ring] at hx
            by_contra! la
            rcases la with ⟨l1, l2⟩

            -- we rewrite la by two cases
            replace la: (a < 1 ∨ 2 < a) ∨ (1 < a ∧ a < 2) := by
                by_cases l: a < 1
                .
                    left
                    left
                    exact l
                .
                    simp at l
                    by_cases l3: a < 2
                    .
                        right
                        simp [l3]
                        by_contra! o
                        replace o: a = 1 := by linarith
                        simp [o] at l1
                    .
                        left
                        simp at l3
                        right
                        by_contra! o
                        replace o: a = 2 := by linarith
                        simp [o] at l2

            rcases la with l | l
            -- case1: a < 1 ∧ 2 < a, we show that the solution is not unique
            .
                clear hx
                clear l1 l2
                have h: ∃ y1 y2, y1 ≠ y2 ∧ y1 ^ 2 + 2 * a * y1 + 3 * a = 2
                    ∧ y2 ^ 2 + 2 * a * y2 + 3 * a = 2 := by
                    rcases l with l | l
                    -- case a < 1
                    .
                        have la: 0 < a ^ 2 - 3 * a + 2 := by
                            nlinarith
                        let y1:= √(a ^ 2 - 3 * a + 2) - a
                        let y2:= -√(a ^ 2 - 3 * a + 2) - a
                        have hy1: y1 + a = √(a ^ 2 - 3 * a + 2) := by
                            simp [y1]
                        replace hy1: (y1 + a) ^ 2 = a ^ 2 - 3 * a + 2 := by
                            rw [hy1]
                            symm
                            rw [← Real.sqrt_eq_iff_eq_sq]
                            linarith
                            apply Real.sqrt_nonneg
                        have hy2: y2 + a = -√(a ^ 2 - 3 * a + 2) := by
                            simp [y2]
                        replace hy2: (y2 + a) ^ 2 = a ^ 2 - 3 * a + 2 := by
                            rw [hy2]
                            symm
                            rw [show (-√(a ^ 2 - 3 * a + 2)) ^ 2
                            = (√(a ^ 2 - 3 * a + 2)) ^ 2 by ring]
                            rw [← Real.sqrt_eq_iff_eq_sq]
                            linarith
                            apply Real.sqrt_nonneg
                        use y1
                        use y2
                        constructor
                        .
                            simp [y1,y2]
                            have o: 0 < √(a ^ 2 - 3 * a + 2) := by
                                have s: 0 ≤ √(a ^ 2 - 3 * a + 2) := by
                                    apply Real.sqrt_nonneg
                                by_contra! o
                                replace o: (√(a ^ 2 - 3 * a + 2)) ^ 2 = 0 := by nlinarith
                                have t: (√(a ^ 2 - 3 * a + 2)) ^ 2 = a ^ 2 - 3 * a + 2 := by
                                    symm
                                    rw [← Real.sqrt_eq_iff_eq_sq]
                                    linarith
                                    apply Real.sqrt_nonneg
                                rw [t] at o
                                simp [o] at la
                            nlinarith
                        .
                            constructor
                            .
                                nlinarith [hy1]
                            .
                                nlinarith [hy2]
                    -- case 2 < a
                    .
                        have la: 0 < a ^ 2 - 3 * a + 2 := by
                            nlinarith
                        let y1:= √(a ^ 2 - 3 * a + 2) - a
                        let y2:= -√(a ^ 2 - 3 * a + 2) - a
                        have hy1: y1 + a = √(a ^ 2 - 3 * a + 2) := by
                            simp [y1]
                        replace hy1: (y1 + a) ^ 2 = a ^ 2 - 3 * a + 2 := by
                            rw [hy1]
                            symm
                            rw [← Real.sqrt_eq_iff_eq_sq]
                            linarith
                            apply Real.sqrt_nonneg
                        have hy2: y2 + a = -√(a ^ 2 - 3 * a + 2) := by
                            simp [y2]
                        replace hy2: (y2 + a) ^ 2 = a ^ 2 - 3 * a + 2 := by
                            rw [hy2]
                            symm
                            rw [show (-√(a ^ 2 - 3 * a + 2)) ^ 2
                            = (√(a ^ 2 - 3 * a + 2)) ^ 2 by ring]
                            rw [← Real.sqrt_eq_iff_eq_sq]
                            linarith
                            apply Real.sqrt_nonneg
                        use y1
                        use y2
                        constructor
                        .
                            simp [y1,y2]
                            have o: 0 < √(a ^ 2 - 3 * a + 2) := by
                                have s: 0 ≤ √(a ^ 2 - 3 * a + 2) := by
                                    apply Real.sqrt_nonneg
                                by_contra! o
                                replace o: (√(a ^ 2 - 3 * a + 2)) ^ 2 = 0 := by nlinarith
                                have t: (√(a ^ 2 - 3 * a + 2)) ^ 2 = a ^ 2 - 3 * a + 2 := by
                                    symm
                                    rw [← Real.sqrt_eq_iff_eq_sq]
                                    linarith
                                    apply Real.sqrt_nonneg
                                rw [t] at o
                                simp [o] at la

                            nlinarith
                        .
                            constructor
                            .
                                nlinarith [hy1]
                            .
                                nlinarith [hy2]

                -- hence we can use get contradiction at hy
                obtain ⟨y1, y2, ne, h1, h2⟩ := h
                have c1:= hy y1
                simp at c1
                rw [h1] at c1
                norm_num at c1
                have c2:= hy y2
                simp at c2
                rw [h2] at c2
                norm_num at c2
                rw [← c1] at c2
                simp [c2] at ne

            -- case2: 1 < a < 2, we show that there are no solution
            .
                clear l1 l2
                rcases l with ⟨l, r⟩
                have eq: |(x + a) ^ 2 + 3 * a - a ^ 2| = (x + a) ^ 2 + 3 * a - a ^ 2 := by
                    apply abs_of_nonneg
                    nlinarith
                rw [eq] at hx
                clear eq hy
                absurd hx
                simp
                nlinarith


        -- the backward direction
        .
            intro h
            rcases h with h | h
            .
                simp [h]
                use -1
                constructor
                .
                    norm_num
                .
                    intro y hy
                    clear h
                    have o: |y ^ 2 + 2 * y + 3| = y ^ 2 + 2 * y + 3 := by
                        apply abs_of_nonneg
                        nlinarith
                    rw [o] at hy
                    replace hy: (y + 1) ^ 2 ≤ 0 := by
                        nlinarith
                    nlinarith
            .
                simp [h]
                norm_num
                use -2
                constructor
                .
                    norm_num
                .
                    intro y hy
                    clear h
                    have o: |y ^ 2 + 4 * y + 6| = y ^ 2 + 4 * y + 6 := by
                        apply abs_of_nonneg
                        rw [show y ^ 2 + 4 * y + 6 = (y + 2) ^ 2 + 2 by ring]
                        nlinarith
                    rw [o] at hy
                    replace hy: (y + 2) ^ 2 ≤ 0 := by
                        nlinarith
                    nlinarith


    -- then we can count the card
    rw [h_eq]
    simp [Set.encard]