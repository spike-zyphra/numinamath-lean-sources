import Mathlib

open Real

theorem inequalities_220505 (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (2 * i + 1)^2 : ℝ) < 1 / 4 := by

  have h1 : ∀ (i : ℕ), i ≥ 1 → (1 : ℝ) / ((2 * i + 1 : ℝ) ^ 2) < (1 : ℝ) / (4 * ((i : ℝ) * (i + 1 : ℝ))) := by
    intro i hi
    have h2 : (2 * i + 1 : ℝ) ^ 2 > (4 * ((i : ℝ) * (i + 1 : ℝ))) := by
      have h3 : (i : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast (show i ≥ 1 by linarith)
      nlinarith [sq_nonneg ((i : ℝ)), sq_nonneg ((i + 1 : ℝ))]
    have h3 : (4 * ((i : ℝ) * (i + 1 : ℝ))) > 0 := by
      have h3 : (i : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast (show i ≥ 1 by linarith)
      nlinarith [sq_nonneg ((i : ℝ)), sq_nonneg ((i + 1 : ℝ))]
    have h4 : (2 * i + 1 : ℝ) ^ 2 > 0 := by
      have h3 : (i : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast (show i ≥ 1 by linarith)
      nlinarith [sq_nonneg ((i : ℝ)), sq_nonneg ((i + 1 : ℝ))]
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  have h2 : ∑ i in Finset.Icc 1 n, (1 / (2 * i + 1)^2 : ℝ) < ∑ i in Finset.Icc 1 n, (1 / (4 * (i * (i + 1)) : ℝ)) := by
    apply Finset.sum_lt_sum
    · -- Show that for all i in the range, term1 < term2
      intro i hi
      have h3 : i ≥ 1 := by
        have h3 : i ∈ Finset.Icc (1 : ℕ) n := by
          exact hi
        simp at h3 ⊢
        all_goals omega
      have h4 : (1 / (2 * i + 1)^2 : ℝ) < (1 / (4 * (i * (i + 1)) : ℝ)) := by
        apply h1 i (by linarith)
      linarith
    · -- Show that exists an i in the range, term1 < term2
      use 1
      constructor
      · -- Show 1 ∈ Finset.Icc 1 n
        simp at *
        all_goals omega
      · -- Show term1 < term2 at i = 1
        specialize h1 1 (by linarith)
        simpa using h1

  have h3 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, (1 / (4 * (i * (i + 1)) : ℝ)) = (1 : ℝ) / 4 * (1 - 1 / ((n + 1 : ℝ))) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp at *
      ring_nf at *

  have h4 : ∑ i in Finset.Icc 1 n, (1 / (4 * (i * (i + 1)) : ℝ)) = (1 : ℝ) / 4 * (1 - 1 / ((n + 1 : ℝ))) := h3 n

  have h5 : (1 : ℝ) / 4 * (1 - 1 / ((n + 1 : ℝ))) < (1 / 4 : ℝ) := by
    have h6 : (1 - 1 / ((n + 1 : ℝ)) : ℝ) < (1 : ℝ) := by
      have h7 : (1 / ((n + 1 : ℝ)) : ℝ) > 0 := by
        apply div_pos
        norm_num
        have h8 : (n + 1 : ℝ) > 0 := by
          have h9 : (n : ℝ) ≥ 0 := by
            exact_mod_cast (show n ≥ 0 by omega)
          nlinarith
        linarith
      nlinarith
    nlinarith

  linarith [h2, h4, h5]