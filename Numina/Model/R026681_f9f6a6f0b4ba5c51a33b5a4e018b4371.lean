import Mathlib

open Real
open scoped BigOperators

theorem inequalities_327261 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) :
  ∑ i, ((a i + 1 / a i)^2 : ℝ) ≥ (n^2 + 1) / n := by
  have h1 : ∀ i, (a i + 1 / a i) ^ 2 ≥ 4 := by
    intro i
    have ha1 : 0 < a i := ha i
    have h6 : a i * (1 / a i) = 1 := by
      field_simp
    nlinarith [sq_nonneg (a i - 1 / a i), sq_nonneg (a i), sq_nonneg (1 / a i - a i), sq_nonneg (a i * (1 / a i) - 1), mul_pos ha1 (show 0 < 1 / a i by
      apply div_pos
      linarith
      all_goals linarith [ha1]
    )
  ]

  have h2 : ∑ i, ((a i + 1 / a i)^2 : ℝ) ≥ 4 * (n : ℝ) := by
    calc
      ∑ i, ((a i + 1 / a i)^2 : ℝ) ≥ ∑ i, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        specialize h1 i
        linarith
      _ = 4 * (n : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ]
        <;> ring_nf <;> norm_num

  have h3 : (4 * (n : ℝ)) ≥ (n ^ 2 + 1) / (n : ℝ) := by
    have hn1 : (n : ℝ) > 0 := by
      exact_mod_cast show (n : ℕ) > 0 by exact hn
    have h5 : (n : ℕ) ≥ 1 := by linarith
    have h6 : (n : ℝ) ≥ (1 : ℝ) := by
      exact_mod_cast h5
    have h7 : (n : ℝ) ^ 2 ≥ (1 : ℝ) / 3 := by
      nlinarith
    have h8 : (n^2 + 1 : ℝ) / (n : ℝ) ≤ (4 * (n : ℝ)) := by
      have hn1' : (n : ℝ) > 0 := hn1
      apply (div_le_iff₀ (by linarith : (n : ℝ) > 0)).mpr
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1 / 3), sq_nonneg ((n : ℝ) - 1 / 2), sq_nonneg ((n : ℝ) * 2 - 1 / 2)
        ]
    linarith

  linarith [h2, h3]