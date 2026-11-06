import Mathlib

open Real

theorem algebra_137923 {f : ℕ → ℝ} (hf : ∀ n, f n = (∑ i in Finset.Icc 1 n, i) / ((n + 32) * ∑ i in Finset.Icc 1 (n + 1), i)) :
    IsGreatest (Set.image f {n | 0 < n}) (1 / 50) := by

  have h1 : ∀ n, f n = (∑ i in Finset.Icc 1 n, (i : ℝ)) / ((n + 32) * ∑ i in Finset.Icc 1 (n + 1), (i : ℝ)) := by
    intro n
    specialize hf n
    simpa using hf

  have h2 : ∀ n : ℕ, (∑ i in Finset.Icc 1 n, (i : ℝ)) = ((n : ℝ) * (n + 1) / 2) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      field_simp
      ring

  have h3 : ∀ n, f n = ( (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) ) := by 
    intro n
    rw [h1 n]
    rw [h2 n, h2 (n + 1)]
    field_simp
    ring_nf

  have h4 : 1 / 50 ∈ Set.image f {n | 0 < n} := by
    use 8
    constructor 
    · norm_num
    · rw [h3 8]
      norm_num

  have h5 : ∀ y ∈ Set.image f {n | 0 < n}, y ≤ 1 / 50 := by
    intro y hy
    rcases hy with ⟨n, hn, hyn⟩
    have hn1 : 0 < n := by 
      simpa using hn
    have h6 : f n = ( (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) ) := h3 n
    rw [h6] at hyn
    have hn2 : (n : ℝ) > 0 := by
      have hn' : n > 0 := by simpa using hn
      exact_mod_cast hn'
    have hn3 : (n + 32 : ℝ) > 0 := by 
      nlinarith
    have hn4 : (n + 2 : ℝ) > 0 := by 
      nlinarith
    have h8 : (n : ℝ) / ((n + 32 : ℝ) * (n + 2 : ℝ)) ≤ (1 / 50 : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((n : ℝ) - 8)]
    linarith

  constructor
  · exact h4
  · exact h5