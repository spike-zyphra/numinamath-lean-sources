import Mathlib

open Finset Real

theorem algebra_244930 {f : ℕ → ℝ} (hf : ∀ n, f n = (∑ i in range n, (i + 1)) / ((n + 32) * ∑ i in range (n + 1), (i + 1))) :
    IsGreatest (Set.image f {n | 0 < n}) (1 / 50) := by
  have h1 : ∀ n : ℕ, f n = (∑ i in range n, (i + 1 : ℝ)) / ((n + 32 : ℝ) * ∑ i in range (n + 1), (i + 1 : ℝ)) := by
    intro n
    specialize hf n
    simpa using hf
  have h2 : ∀ n : ℕ, (∑ i in range n, (i + 1 : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => 
      rw [sum_range_succ, ih]
      field_simp
      ring
  have h3 : ∀ n : ℕ, f n = (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) := by
    intro n
    rw [h1 n]
    rw [h2 n, h2 (n + 1)]
    field_simp
    ring
  constructor
  · -- Show that 1/50 is in the image of f for n > 0
    use 8
    constructor
    · -- Show that 8 > 0
      norm_num
    · -- Show that f 8 = 1 / 50
      rw [h3 8]
      norm_num
  · -- Show that 1/50 is an upper bound for the image of f
    intro y hy
    rcases hy with ⟨n, hn, hyn⟩
    have h4 : n > 0 := by 
      simpa using hn
    have hn_n : (n : ℝ) > (0 : ℝ) := by
      exact_mod_cast h4
    have h5 : f n = (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) := h3 n
    rw [h5] at hyn
    have hn_pos1 : (n : ℝ) > (0 : ℝ) := by
      exact_mod_cast h4
    have hn_pos2 : (n + 32 : ℝ) > (0 : ℝ) := by
      nlinarith [show (n : ℝ) > (0 : ℝ) by exact_mod_cast h4]
    have hn_pos3 : (n + 2 : ℝ) > (0 : ℝ) := by
      nlinarith [show (n : ℝ) > (0 : ℝ) by exact_mod_cast h4]
    have h7 : (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) ≤ (1 / 50 : ℝ) := by
      have h8 : (n : ℝ) * 50 ≤ (n + 32 : ℝ) * (n + 2 : ℝ) := by
        nlinarith [sq_nonneg ((n : ℝ) - 8), sq_nonneg ((n : ℝ))]
      have h9 : (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) ≤ (1 / 50 : ℝ) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h8]
      exact h9
    linarith [hyn, h7]