import Mathlib

/-Prove that there are only finitely many ordered triples (x−y,y−z,z−x)
of complex numbers that satisfy the equations
x * (x - 1) + 2 * y * z = y * (y - 1) + 2 * x * z = z * (z - 1) + 2 * x * y -/

-- we show a useful lemma of the norm form of prod.mk
lemma prod_norm {p: ℂ × ℂ × ℂ}: p = (p.1, p.2.1, p.2.2) := by
     calc
        p = (p.1, p.2) := by simp
        _ = (p.1, p.2.1, p.2.2) := by simp

theorem algebra_216466 :
    Set.Finite {(a, b, c): ℂ × ℂ × ℂ | ∃ x y z, a = x - y ∧ b = y - z ∧ c = z - x ∧
    x * (x - 1) + 2 * y * z = y * (y - 1) + 2 * x * z ∧
    y * (y - 1) + 2 * x * z = z * (z - 1) + 2 * x * y} := by

    -- we directly compute the solutions
    have h_subset : {(a, b, c): ℂ × ℂ × ℂ | ∃ x y z, a = x - y ∧ b = y - z ∧ c = z - x ∧
    x * (x - 1) + 2 * y * z = y * (y - 1) + 2 * x * z ∧
    y * (y - 1) + 2 * x * z = z * (z - 1) + 2 * x * y} ⊆ {(0, 0, 0), (0, -1, 1), (1, 0, -1), (-1, 1, 0)} := by
        intro p
        intro h
        simp only [Set.mem_setOf_eq] at h
        obtain ⟨x, y, z, h1, h2, h3, f1, f2⟩ := h
        simp
        have l: p = (p.1, p.2.1, p.2.2) := by apply prod_norm
        rw [l]
        set a:= p.1
        set b:= p.2.1
        set c:= p.2.2
        clear_value a b c
        clear l
        simp

        -- write the terms in the form of a, b, c
        have g1: x = a + y := by
            simp [h1]
        have g2: z = y - b := by
            simp [h2]
        have g3: c = - (a + b) := by
            simp [h1, h2, h3]
        simp [g1, g2] at f1 f2

        -- simplify the equations
        replace f1: (a + y) * (a + y - 1) + 2 * y * (y - b) - (y * (y - 1) + 2 * (a + y) * (y - b)) = 0 := by
            rw [f1]
            ring
        ring_nf at f1

        replace f2: y * (y - 1) + 2 * (a + y) * (y - b) - ((y - b) * (y - b - 1) + 2 * (a + y) * y) = 0 := by
            rw [f2]
            ring
        ring_nf at f2
        replace f1: a * (b * 2 + a - 1) = 0 := by
            rw [← f1]
            ring
        simp at f1
        rcases f1 with f1 | f1

        -- case 1: a = 0
        .
            simp [f1]
            simp [f1] at f2
            rw [show -b - b ^ 2 = -b * (b + 1) by ring] at f2
            simp at f2
            rcases f2 with f2 | f2
            .
                simp [f2]
                simp [f1, f2] at g3
                simp [g3]
            .
                replace f2: b = -1 := by
                    rw [show b = b + 1 - 1 by ring]
                    simp [f2]
                simp [f2, f1] at *
                exact g3

        -- case 2: a ≠ 0
        .
            replace f1: b = (1 - a) / 2 := by
                field_simp
                rw [show b * 2 = b * 2 + a - 1 + 1 - a by ring]
                simp [f1]
            simp [f1] at f2
            field_simp at f2
            ring_nf at f2
            rw [show -6 + a ^ 2 * 6 = 6 * (a + 1) * (a - 1) by ring] at f2
            simp at f2
            rcases f2 with f2 | f2
            .
                replace f2: a = -1 := by
                    rw [show a = a + 1 - 1 by ring]
                    simp [f2]
                simp [f2] at f1
                simp [f1, f2]
                simp [f1, f2] at g3
                exact g3
            .
                replace f2: a = 1 := by
                    rw [show a = a - 1 + 1 by ring]
                    simp [f2]
                simp [f2] at f1
                simp [f1, f2] at g3
                simp [f1, f2, g3]


    have hs: ({(0, 0, 0), (0, -1, 1), (1, 0, -1), (-1, 1, 0)}: Set (ℂ × ℂ × ℂ)).Finite := by
        clear h_subset
        have o: ({(0, 0, 0), (0, -1, 1), (1, 0, -1), (-1, 1, 0)}: Set (ℂ × ℂ × ℂ)).encard = 4 := by
            repeat rw [Set.encard_insert_of_not_mem]
            norm_num
            simp
            simp
            simp
            constructor
            .
                by_contra! r
                symm at r
                rw [Prod.mk_eq_zero] at r
                simp at r
            .
                constructor
                .
                    by_contra! r
                    symm at r
                    rw [Prod.mk_eq_zero] at r
                    simp at r
                .
                    by_contra! r
                    symm at r
                    rw [Prod.mk_eq_zero] at r
                    simp at r
        exact Set.finite_of_encard_eq_coe o

    exact Set.Finite.subset hs h_subset
    