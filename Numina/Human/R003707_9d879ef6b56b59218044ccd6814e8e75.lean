import Mathlib

set_option maxHeartbeats 600000

/-Solve the equation
abcdefg=a+b+c+d+e+f+g in natural numbers.-/

theorem number_theory_209357: {(a, b, c, d, e, f, g): ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
  a * b * c * d * e * f * g = a + b + c + d + e + f + g ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ f ∧ f ≤ g}
    = {(0, 0, 0, 0, 0, 0, 0), (1, 1, 1, 1, 1, 2, 7), (1, 1, 1, 1, 1, 3, 4)} := by

      ext ⟨a, b, c, d, e, f, g⟩
      constructor

      -- the forward direction
      .
        intro h
        simp at h
        rcases h with ⟨h, l1, l2, l3, l4, l5, l6⟩
        simp
        by_cases s: a = 0

        -- case a = 0, then the rest are all 0
        .
          left
          simp [s] at h
          omega
        .
          -- we show that a = 1
          have va: a = 1 := by
            by_contra! o
            have la: 2 ≤ a := by
              omega
            have lb: 2 ≤ b := by omega
            have f1: 4 ≤ a * b := by nlinarith
            have f2: 8 ≤ a * b * c := by nlinarith
            have f3: 8 ≤ a * b * c * d := by nlinarith
            have f4: 8 ≤ a * b * c * d * e := by nlinarith
            have f5: 8 ≤ a * b * c * d * e * f := by nlinarith
            have f6: 8 * g ≤ a * b * c * d * e * f * g:= by nlinarith
            rw [h] at f6
            clear f1 f2 f3 f4 f5
            omega
          simp [va] at *

          -- b = 1
          have vb: b = 1 := by
            by_contra! o
            have lb: 2 ≤ b := by
              omega
            have lb: 2 ≤ b := by omega
            have f1: 4 ≤ b * c := by nlinarith
            have f2: 8 ≤ b * c * d := by nlinarith
            have f3: 8 ≤ b * c * d * e := by nlinarith
            have f4: 8 ≤ b * c * d * e * f:= by nlinarith
            have f6: 8 * g ≤ b * c * d * e * f * g:= by nlinarith
            rw [h] at f6
            clear f1 f2 f3 f4
            omega
          simp [vb] at *

         -- c = 1
          have vc: c = 1 := by
            by_contra! o
            have lc: 2 ≤ c := by omega
            have f1: 4 ≤ c * d := by nlinarith
            have f2: 8 ≤ c * d * e := by nlinarith
            have f3: 8 ≤ c * d * e * f:= by nlinarith
            have f6: 8 * g ≤ c * d * e * f * g:= by nlinarith
            rw [h] at f6
            clear f1 f2 f3
            omega
          simp [vc] at *

        -- d = 1
          have vd: d = 1 := by
            by_contra! o
            have ld: 2 ≤ d := by omega
            have f1: 4 ≤ d * e := by nlinarith
            have f2: 8 ≤ d * e * f := by nlinarith
            have f6: 8 * g ≤ d * e * f * g:= by nlinarith
            rw [h] at f6
            clear f1 f2
            omega
          simp [vd] at *

        -- e = 1
          have ve: e = 1 := by
            by_contra! o
            have le: 2 ≤ e := by omega
            have f1: 4 ≤ e * f := by nlinarith
            have f6: 4 * g ≤ e * f * g:= by nlinarith
            rw [h] at f6
            clear f1
            replace f6: g ≤ 4 := by omega
            have rg: 2 ≤ g := by omega
            interval_cases g
            .
              have vf: f = 2 := by omega
              simp [vf] at h
              omega
            .
              have le: e ≤ 3 := by omega
              have re: 2 ≤ e := by omega
              have ve: e = 2 ∨ e = 3 := by omega
              rcases ve with t | t
              .
                simp [t] at h
                omega
              .
                simp [t] at h
                omega
            .
              have ve: e = 2 ∨ e = 3 ∨ e = 4 := by omega
              rcases ve with t | t | t
              .
                simp [t] at h
                omega
              .
                simp [t] at h
                omega
              .
                simp [t] at h
                omega
          simp [ve] at *

          by_cases u: f ≤ 2

          -- f ≤ 2
          .
            have r: f = 1 ∨ f = 2 := by omega
            rcases r with r | r
            .
              simp [r] at h
            .
              simp [r] at h
              left
              omega

          -- 3 ≤ f
          .
            have rg: g ≤ 5 := by nlinarith
            simp at u
            have lg: 3 ≤ g := by omega
            have m: g = 3 ∨ g = 4 ∨ g = 5 := by omega
            rcases m with m | m | m
            .
              simp [m] at h
              omega
            .
              simp [m] at h
              omega
            .
              simp [m] at h
              omega


      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h | h
        .
          simp [h]
        .
          simp [h]
        .
          simp [h]