import Mathlib

def S (n : ℕ) := ∑ i in Finset.Icc 1 n, i

theorem algebra_115472 {f : ℕ → ℝ} (hf : ∀ n, f n = S n / ((n + 32) * S (n + 1))) :
    IsGreatest (Set.image f {n | 0 < n}) (1 / 50) := by

  have h1 : ∀ n, S n = (n : ℝ) * (n + 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp [S]
    | succ n ih =>
      have h2 : S (n + 1) = S n + ((n + 1 : ℕ) : ℝ) := by
        simp [S, Finset.sum_Icc_succ_top, add_assoc]
      rw [h2, ih]
      field_simp at *
      ring_nf

  constructor
  · -- First part: show that 1/50 is in the image of f when n > 0
    use 8
    constructor
    · norm_num
    · -- Show that $f(8) = 1/50$
      rw [hf 8]
      rw [h1 8, h1 9]
      norm_num

  · -- Second part: show that 1/50 is the greatest value
    intro y hy
    rcases hy with ⟨n, hn, hyn⟩
    have hn_pos : 0 < n := by
      simpa using hn

    have h4 : f n = S n / ((n + 32) * S (n + 1)) := hf n
    rw [h4] at hyn

    have h5 : (S n : ℝ) = (n : ℝ) * (n + 1) / 2 := h1 n
    have h6 : (S (n + 1) : ℝ) = ((n + 1 : ℝ)) * ((n + 1 + 1 : ℝ)) / 2 := by
      have h7 : S (n + 1) = ((n + 1 : ℕ) : ℝ) * ((n + 1 + 1 : ℝ)) / 2 := by
        specialize h1 (n + 1)
        simpa using h1
      simpa using h7

    rw [h5, h6] at hyn

    have h7 : (n : ℝ) > 0 := by
      have h8 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast show (0 : ℕ) < n by linarith
      linarith

    have h9 : (n : ℝ) * (n + 1) / 2 / ((n + 32) * (( (n + 1 : ℝ) ) * ((n + 1 + 1 : ℝ)) / 2)) ≤ (1 / 50 : ℝ) := by
      have h10 : (n : ℝ) * (n + 1) / 2 / ((n + 32) * (( (n + 1 : ℝ) ) * ((n + 1 + 1 : ℝ)) / 2)) = (n : ℝ) / ((n + 32) * ((n + 1 + 1 : ℝ)))
        := by
        field_simp
        all_goals
          ring_nf
      rw [h10]
      have h11 : (n + 32) * ((n + 1 + 1 : ℝ)) > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((n : ℝ) - 8 : ℝ)]

    nlinarith