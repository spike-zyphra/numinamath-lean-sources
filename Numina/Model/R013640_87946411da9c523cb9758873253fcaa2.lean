import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225160 {x : ℝ} (hx : x ∈ Icc 0 (2 * π)) :
    ∃ a b : ℤ, 3 * sin x = a ∧ (4 / 7) * cos (2 * x) + (5 / 3) * sin x = b ↔
    x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
  have h1 : 0 ≤ x ∧ x ≤ 2 * π := by
    simpa using hx
  use 1, 1
  constructor
  · -- Assume 3 * sin x = 1 ∧ (4 / 7) * cos (2 * x) + (5 / 3) * sin x = 1, prove x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3)
    intro h
    rcases h with ⟨h3, h4⟩
    have h6 : sin x = 1 / 3 := by
      have h7 : (3 : ℝ) * sin x = (1 : ℝ) := by
        simpa using h3
      linarith
    have hcos2x : cos (2 * x) = 7 / 9 := by
      have h2sin : sin x = 1 / 3 := h6
      have hcos2x : cos (2 * x) = 1 - 2 * (sin x)^2 := by
        rw [cos_two_mul, sin_sq]
        all_goals
          try linarith
          <;> try ring
          <;> try linarith
      rw [hcos2x, h2sin]
      norm_num
      all_goals try nlinarith
    have hsin : sin x = 1 / 3 := h6
    have h2range : 0 ≤ x ∧ x ≤ 2 * π := h1
    have hx1 : x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
      have h5 : sin x = 1 / 3 := h6
      have hrange0 : 0 ≤ x := h1.left
      have hrange1 : x ≤ 2 * π := h1.right
      by_cases h2pi : x ≤ π
      · -- Assume x ∈ [0, π]
        have hx2 : x ≤ π := h2pi
        have h2i : x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
          have h5pi2 : arcsin (1 / 3) ≤ π / 2 := by
            have h5pi2 : arcsin (1 / 3) ≤ π / 2 := by
              linarith [Real.arcsin_le_pi_div_two (1 / 3)]
            linarith
          have h5pi1 : 0 ≤ arcsin (1 / 3) := by
            apply Real.arcsin_nonneg.mpr
            norm_num
          by_cases hpi2 : x ≤ π / 2
          · -- Assume x ∈ [0, π/2]
            have h2 : arcsin (sin x) = x := by
              rw [Real.arcsin_sin]
              all_goals
                try linarith [show 0 ≤ x by exact hrange0, show x ≤ 2 * π from by linarith, hpi2, h2pi]
            have h4 : arcsin (1 / 3) = arcsin (sin x) := by
              rw [show sin x = 1 / 3 by linarith [h5]]
            have h4' : arcsin (1 / 3) = x := by
              linarith [h2, h4]
            left
            linarith
          · -- Assume x ∈ (π/2, π]
            have h3pi2 : π / 2 < x := by
              by_contra h
              push_neg at h
              have : x ≤ π / 2 := by linarith
              contradiction
            have h3pi2 : π / 2 < x := h3pi2
            have h4pi : x ≤ π := h2pi
            have h5 : arcsin (sin x) = π - x := by
              have h2 : arcsin (sin x) = arcsin (sin (π - x)) := by
                rw [show sin x = sin (π - x) by rw [sin_pi_sub]]
                all_goals try linarith
              rw [h2]
              have h5pi2 : -(π / 2) ≤ π - x := by
                linarith
                -- linarith [h3pi2, hpi2, h1]
              have h5pi3 : π - x ≤ π / 2 := by
                nlinarith
                -- linarith [h3pi2, hpi2, h1]
              have h6 : arcsin (sin (π - x)) = π - x := by
                apply Real.arcsin_sin
                all_goals
                  try linarith [h3pi2, hrange0, hrange1, h2pi]
                  <;> try all_goals linarith
                all_goals try all_goals nlinarith
                all_goals try all_goals tauto
                all_goals try all_goals ring
              linarith
            have h5 : arcsin (1 / 3) = arcsin (sin x) := by
              rw [show sin x = 1 / 3 by linarith [h5]]
            have h4' : π - x = arcsin (1 / 3) := by
              nlinarith [h5, h5]
            right
            linarith
            all_goals try nlinarith
        tauto
      · -- Assume x > π
        have h2pi : π < x := by
          nlinarith
        exfalso
        have h7 : sin x ≤ 0 := by
          have h11 : sin x = sin (x - 2 * π + 2 * π) := by ring
          rw [h11]
          have h9 : sin (x - 2 * π + 2 * π) = sin (x - 2 * π) := by
            rw [sin_add, sin_two_pi, cos_two_pi]
            all_goals
              try ring
              <;> try simp [sin_add, cos_add, sin_sub, cos_sub]
          rw [h9]
          have h8 : π < x := h2pi
          have h12 : 0 < x - 2 * π + π := by
            nlinarith [h8]
          have h7 : sin (x - 2 * π) ≤ 0 := by
            have h0 : sin (x - 2 * π) ≤ 0 := by
              apply sin_nonpos_of_nonnpos_of_neg_pi_le
              · -- Show that x - 2 * π ≤ 0
                nlinarith [show x ≤ 2 * π by linarith [h1.right], h2pi]
                -- Show that x - 2 * π ≤ 0
              · -- Show that -π ≤ x - 2 * π
                nlinarith [show π > 0 by exact Real.pi_pos]
            linarith
          nlinarith
        nlinarith [h7, h6]
    tauto
  · -- Assume x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3), prove 3 * sin x = 1 ∧ (4 / 7) * cos (2 * x) + (5 / 3) * sin x = 1
    rintro (h | h)
    · -- Case x = arcsin (1 / 3)
      have h6 : sin x = 1 / 3 := by
        rw [h]
        apply Real.sin_arcsin
        all_goals
          try norm_num
          <;> try nlinarith [Real.arcsin_le_pi_div_two (1 / 3), Real.neg_pi_div_two_le_arcsin (1 / 3)]
          <;> try all_goals nlinarith
      have h7 : cos (2 * x) = 7 / 9 := by
        have h6sin : sin x = 1 / 3 := h6
        have hcos2x : cos (2 * x) = 1 - 2 * (sin x)^2 := by
          rw [cos_two_mul, sin_sq]
          all_goals
            try linarith
            <;> try ring
            <;> try nlinarith
        rw [hcos2x, h6sin]
        norm_num
      constructor
      · -- 3 * sin x = 1
        have h6_eq : (3 * sin x : ℝ) = (1 : ℝ) := by
          rw [h6]
          norm_num
        norm_num at h6_eq ⊢
        try linarith
      · -- (4 / 7) * cos (2 * x) + (5 / 3) * sin x = 1
        have h_eq : (4 / 7 : ℝ) * cos (2 * x) + (5 / 3) * sin x = (1 : ℝ) := by
          rw [h7, h6]
          norm_num
        norm_num at h_eq ⊢
        try linarith
    · -- Case x = π - arcsin (1 / 3)
      have h6 : sin x = 1 / 3 := by
        rw [h]
        have hsin : sin (π - arcsin (1 / 3)) = sin (arcsin (1 / 3)) := by
          rw [sin_pi_sub]
        have h1 : sin (arcsin (1 / 3)) = (1 / 3 : ℝ) := by
          apply Real.sin_arcsin
          all_goals norm_num
        linarith [hsin, h1]
      have h7 : cos (2 * x) = 7 / 9 := by
        have h6sin : sin x = 1 / 3 := h6
        have hcos2x : cos (2 * x) = 1 - 2 * (sin x)^2 := by
          rw [cos_two_mul, sin_sq]
          all_goals
            try linarith
            <;> try ring
            <;> try nlinarith
        rw [hcos2x, h6sin]
        norm_num
      constructor
      · -- 3 * sin x = 1
        have h6_eq : (3 * sin x : ℝ) = (1 : ℝ) := by
          rw [h6]
          norm_num
        norm_num at h6_eq ⊢
        try linarith
      · -- (4 / 7) * cos (2 * x) + (5 / 3) * sin x = 1
        have h_eq : (4 / 7 : ℝ) * cos (2 * x) + (5 / 3) * sin x = (1 : ℝ) := by
          rw [h7, h6]
          norm_num
        norm_num at h_eq ⊢
        try linarith