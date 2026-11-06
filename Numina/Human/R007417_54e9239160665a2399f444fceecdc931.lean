import Mathlib

/- Let a,b,c,d be real numbers such that
min (20 * x + 19) (19 * x + 20) = (a * x + b) - |c * x + d|
for all real numbers x. Find a * b + c * d -/
theorem algebra_610068 {a b c d: ℝ} (h: ∀ x: ℝ, min (20 * x + 19) (19 * x + 20) = (a * x + b) - |c * x + d|):
  a * b + c * d = 380 := by

  -- for simplicity, we write the case when c > 0 as a lemma so we can use it twice
  have h_eq: ∀ a b c d: ℝ, (0 < c) ∧ (∀ x: ℝ, min (20 * x + 19) (19 * x + 20) = (a * x + b) - |c * x + d|) →
  a * b + c * d = 380 := by
      intro a b c d h
      rcases h with ⟨hc,h⟩

    -- for sufficiently large x
      have h_pos: ∀ x: ℝ, 1 ≤ x ∧ -(d / c) ≤ x → (a - c - 19) * x = 20 + d - b := by
        intro x hx1
        rcases hx1 with ⟨hx1,hx2⟩
        have h1: 19 * x + 20 = a * x + b - (c * x + d) := by  -- we first eliminate the absolute value and min
          specialize h x
          have eq1: min (20 * x + 19) (19 * x + 20) = 19 * x + 20 := by
            simp
            linarith
          have eq2: |c * x + d| = c * x + d := by
            simp
            calc
              c * x + d ≥  c * -(d / c) + d := by nlinarith
                      _ = 0 := by field_simp;ring
          rw [eq1,eq2] at h
          exact h
        nlinarith
      -- construct such x
      have hx: ∃ x: ℝ, 1 ≤ x ∧ -(d / c) ≤ x := by
        by_cases hd: 0 ≤ d
        . use 1
          constructor
          . linarith
          . have o: -(d / c) ≤ 0 := by
              have o1: 0 ≤ d / c := by
                apply div_nonneg
                linarith
                linarith
              linarith
            nlinarith
        . use 1 + (- (d/c))
          have o: 0 ≤ - (d/c) := by
            have o1: d / c ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              linarith
              linarith
            linarith
          constructor
          . linarith
          . linarith
      obtain ⟨x, hx⟩:= hx
      have hx2: 1 ≤ 2 * x ∧ -(d / c) ≤ 2 * x := by
        rcases hx with ⟨hx1,hx2⟩
        constructor
        . nlinarith
        . nlinarith
      have h1:= h_pos x hx
      have h2:= h_pos (2 * x) hx2
      rw [←h1] at h2
      replace h2: a - c - 19 = 0 := by nlinarith
      replace h1: 20 + d - b = 0 := by nlinarith
      clear h_pos hx hx2

    -- for sufficiently small x, we get another two equations
      have h_neg: ∀ x: ℝ, x ≤ -1 ∧ x ≤ -(d / c)  → (a + c - 20) * x = 19 - b - d:= by
        intro x hx1
        rcases hx1 with ⟨hx1,hx2⟩
        have h1: 20 * x + 19 = a * x + b + (c * x + d) := by  -- we first eliminate the absolute value and min
          specialize h x
          have eq1: min (20 * x + 19) (19 * x + 20) = 20 * x + 19 := by
            simp
            linarith
          have eq2: |c * x + d| = - (c * x + d) := by
            have o: c * x + d ≤ 0 := by
              calc
                c * x + d ≤ c * -(d / c) + d := by nlinarith
                        _ = 0 := by field_simp;ring
            apply abs_of_nonpos
            exact o
          rw [eq1,eq2] at h
          nlinarith
        nlinarith
         -- construct such x
      have hx: ∃ x: ℝ, x ≤ -1 ∧ x ≤ -(d / c) := by
        by_cases hd: d ≤ 0
        . use -1
          constructor
          . linarith
          . have o: -(d / c) ≥  0 := by
              have o1: d / c ≤ 0 := by
                apply div_nonpos_of_nonpos_of_nonneg
                linarith
                linarith
              linarith
            nlinarith
        . simp at hd
          use -1 - (d/c)
          have o: 0 ≤ (d/c) := by
              apply div_nonneg
              linarith
              linarith
          constructor
          . linarith
          . linarith
      obtain ⟨x, hx⟩:= hx
      have hx2: 2 * x ≤ -1 ∧ 2 * x ≤ -(d / c) := by
        rcases hx with ⟨hx1,hx2⟩
        constructor
        . nlinarith
        . nlinarith
      have h3:= h_neg x hx
      have h4:= h_neg (2 * x) hx2
      rw [←h3] at h4
      replace h4: a + c - 20 = 0 := by nlinarith
      replace h3: 19 - b - d = 0 := by nlinarith
      clear h_neg hx hx2 h
      -- Then we can solve a b c d by the four equations
      have ea: a = 39 / 2 := by nlinarith
      have eb: b = 39 / 2 := by nlinarith
      have ec: c = 1 / 2 := by nlinarith
      have ed: d = -1 / 2 := by nlinarith
      nlinarith

  -- Now we can use the lemma to get the result for c ≠ 0
  by_cases hc: 0 < c
  -- for the case when c > 0
  . specialize h_eq a b c d
    simp [hc,h] at h_eq
    exact h_eq
  -- for the case when c ≤ c
  . replace hc: c < 0 ∨ c = 0 := by
      simp at hc
      by_cases hc1: c = 0
      . right
        exact hc1
      . left
        by_contra! no
        absurd hc1
        nlinarith
    rcases hc with hc | hc
    -- for the case when c < 0, we use symmetry given by C = -c and  D = -d
    . set C:= -c with hC
      set D:= -d with hD
      replace hC: c = -C := by linarith
      replace hD: d = -D := by linarith
      have hC1: 0 < C := by linarith
      simp [hC,hD]
      simp [hC,hD] at h
      specialize h_eq a b C D
      simp [hC1] at h_eq
      apply h_eq
      simp [h]
      intro x
      rw [show -(C * x) + -D = - (C * x + D) by ring]
      set y:= C * x + D with hy
      simp
    . clear h_eq
      simp [hc] at h
      simp [hc]
      by_cases hd: 0 ≤ d
      -- for the case when d ≥ 0
      . rw [show |d| = d by simp; exact hd] at h
        have h1:= h 0
        have h2:= h (-1)
        have h3:= h 1
        simp at h1 h2 h3
        rw [show 19 ⊓ 20 = (19: ℝ) by norm_num] at h1
        rw [show (-20 + 19) ⊓ (-19 + 20) = (-1: ℝ) by norm_num] at h2
        rw [show (20 + 19) ⊓ (19 + 20) = (39: ℝ) by norm_num] at h3
        have ea: a = 20 := by nlinarith
        rw [ea] at h
        have h4:= h 2
        rw [show (20 * 2 + 19) ⊓ (19 * 2 + 20) = (58: ℝ) by norm_num] at h4
        ring_nf at h4
        rw [← h1] at h4
        absurd h4
        norm_num
      -- for the case when d < 0
      . rw [show |d| = -d by apply abs_of_nonpos; linarith] at h
        have h1:= h 0
        have h2:= h (-1)
        have h3:= h 1
        simp at h1 h2 h3
        rw [show 19 ⊓ 20 = (19: ℝ) by norm_num] at h1
        rw [show (-20 + 19) ⊓ (-19 + 20) = (-1: ℝ) by norm_num] at h2
        rw [show (20 + 19) ⊓ (19 + 20) = (39: ℝ) by norm_num] at h3
        have ea: a = 20 := by nlinarith
        rw [ea] at h
        have h4:= h 2
        rw [show (20 * 2 + 19) ⊓ (19 * 2 + 20) = (58: ℝ) by norm_num] at h4
        ring_nf at h4
        rw [show 40 + b + d = b + d + 40 by abel] at h4
        rw [← h1] at h4
        absurd h4
        norm_num