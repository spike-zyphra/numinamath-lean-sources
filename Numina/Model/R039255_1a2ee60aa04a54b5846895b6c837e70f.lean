import Mathlib

open Finset Real

theorem algebra_124364 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ k ∈ Icc 1 n, x k = (-1) ^ k) :
    (∑ i ∈ Icc 1 n, x i) / n = 0 ∨ (∑ i ∈ Icc 1 n, x i) / n = -1 / n := by
  have h1 : ∀ i ∈ Icc 1 n, x i = (-1 : ℝ) ^ i := by 
    intro i hi
    specialize hx i hi
    simpa using hx

  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by 
    omega

  cases h2 with
  | inl h_even =>
    have h3 : ∑ i in Icc 1 n, x i = 0 := by
      have h4 : n % 2 = 0 := h_even
      have h6 : ∀ (m : ℕ), ∑ i ∈ Icc 1 (2 * m), ((-1: ℝ) ^ i) = 0 := by
        intro m
        induction m with
        | zero =>
          norm_num [sum_Icc_succ_top]
        | succ m ih =>
          rw [show 2 * (m + 1) = 2 * m + 2 by ring]
          simp [sum_Icc_succ_top, sum_Icc_succ_top, ih] at *
          <;> ring_nf
      have h7 : ∃ m : ℕ, n = 2 * m := by 
        refine' ⟨n / 2, by omega⟩
      rcases h7 with ⟨m, hm⟩
      have h7' : ∑ i in Icc 1 n, x i = ∑ i in Icc 1 n, ((-1 : ℝ) ^ i) := by 
        apply sum_congr 
        · rfl
        · intro i hi
          have h1' : x i = (-1 : ℝ) ^ i := by 
            apply h1 i hi
          simpa using h1'
      rw [h7'] 
      rw [hm]
      specialize h6 m 
      all_goals linarith
    have h4 : (∑ i in Icc 1 n, x i) / n = 0 := by 
      rw [h3] 
      all_goals norm_num 
    left
    exact h4
  | inr h_odd =>
    have h3 : ∑ i in Icc 1 n, x i = -1 := by 
      have h4 : n % 2 = 1 := h_odd
      have h6 : ∀ (m : ℕ), ∑ i ∈ Icc 1 (2 * m + 1), ((-1: ℝ) ^ i) = -1 := by 
        intro m 
        induction m with 
        | zero => 
          norm_num [sum_Icc_succ_top]
        | succ m ih =>
          rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring]
          simp [sum_Icc_succ_top, sum_Icc_succ_top, ih] at *
          <;> ring_nf
      have h7 : ∃ m : ℕ, n = 2 * m + 1 := by
        refine' ⟨(n - 1) / 2, by omega⟩ 
      rcases h7 with ⟨m, hm⟩ 
      have h7' : ∑ i in Icc 1 n, x i = ∑ i in Icc 1 n, ((-1 : ℝ) ^ i) := by
        apply sum_congr 
        · rfl 
        · intro i hi
          have h1' : x i = (-1 : ℝ) ^ i := by 
            apply h1 i hi
          simpa using h1'
      rw [h7'] 
      rw [hm]
      specialize h6 m 
      all_goals linarith
    have h4 : (∑ i in Icc 1 n, x i) / n = -1 / n := by 
      rw [h3] 
      <;> field_simp 
    right
    exact h4