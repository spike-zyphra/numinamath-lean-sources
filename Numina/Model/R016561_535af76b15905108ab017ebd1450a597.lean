import Mathlib

open Real

theorem algebra_8117 {S : ℕ → ℝ} (hS : ∀ n, S n = ∑ i in Finset.Icc 1 n, i) :
    IsGreatest {x | ∃ n, x = S n / ((n + 32) * S (n + 1))} (1 / 50) := by 
  constructor 
  · -- Show that 1/50 is a obtainable
    use 8
    norm_num [hS, Finset.sum_Icc_succ_top]
    <;> norm_num
    <;> ring_nf <;> norm_num
  · -- Show any value in the set is ≤ 1/50
    intro x hx
    rcases hx with ⟨n, hn⟩
    rw [hn]
    have h4 : ∀ n : ℕ, S n = (n : ℝ) * (n + 1) / 2 := by
      intro n
      rw [hS n]
      have h5 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (i : ℝ) = (n : ℝ) * (n + 1) / 2 := by 
        intro n 
        induction n with
        | zero => 
          simp
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by linarith), ih]
          all_goals 
            field_simp at *
            <;> ring_nf <;> linarith
      specialize h5 n
      norm_num at h5 ⊢
      tauto
    have h1 : S n = (n : ℝ) * (n + 1) / 2 := h4 n
    have h2 : S (n + 1) = ((n + 1) : ℝ) * (n + 2) / 2 := by 
      have h5 := h4 (n + 1)
      simp [show (n + 1 : ℕ) + 1 = n + 2 by omega] at h5 ⊢
      <;> nlinarith
    rw [h1, h2]
    have h6 : ((n : ℝ) * (n + 1) / 2) / ((n + 32) * ((n + 1 : ℝ) * (n + 2) / 2)) = (n : ℝ) / ((n + 32) * (n + 2)) := by 
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h6]
    have h7 : (n : ℝ) / ((n + 32) * (n + 2)) ≤ (1 / 50 : ℝ) := by
      have h8 : (n + 32 : ℝ) * (n + 2) - 50 * (n : ℝ) ≥ 0 := by
        nlinarith [sq_nonneg ((n : ℝ) - 8)]
      have h9 : (n + 32 : ℝ) * (n + 2) > 0 := by 
        positivity
      apply (div_le_iff (by positivity)).mpr
      nlinarith
    nlinarith