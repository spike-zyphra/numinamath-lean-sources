import Mathlib

open Real

theorem algebra_166822 {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ x ∈ Set.Icc 4 9, f 0 x = 2 * sqrt x)
    (hfn : ∀ n, ∀ x ∈ Set.Icc 4 9, f (n + 1) x = 4 / (2 - f n x)) :
    f 2023 9 = -1 := by
  have h1 : f 0 9 = 6 := by
    specialize hf0 9 (by norm_num [Set.mem_Icc])
    rw [hf0]
    have h2 : sqrt (9 : ℝ) = 3 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h2]
    norm_num
  have h2 : f 1 9 = -1 := by
    specialize hfn 0 9 (by norm_num [Set.mem_Icc])
    rw [hfn]
    rw [h1]
    norm_num
  have h3 : f 2 9 = 4 / 3 := by
    specialize hfn 1 9 (by norm_num [Set.mem_Icc])
    rw [hfn]
    rw [h2]
    norm_num
  have h4 : f 3 9 = 6 := by
    specialize hfn 2 9 (by norm_num [Set.mem_Icc])
    rw [hfn]
    rw [h3]
    norm_num
  have h5 : ∀ (k : ℕ), f (3 * k + 1) 9 = -1 := by
    intro k
    induction k with
    | zero =>
      norm_num [h2]
    | succ k ih =>
      have h6 : f (3 * (k + 1) + 1) 9 = f (3 * k + 4) 9 := by
        ring_nf
      rw [h6]
      have h7 : 3 * k + 3 ≥ 0 := by omega
      have h8 : 3 * k + 2 ≥ 0 := by omega
      have h9 : 3 * k + 1 ≥ 0 := by omega
      have h10 : f (3 * k + 4) 9 = 4 / (2 - f (3 * k + 3) 9) := by
        specialize hfn (3 * k + 3) 9 (by
          have h10 : (4 : ℝ) ≤ 9 := by norm_num
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
        )
        simpa using hfn
      have h11 : f (3 * k + 3) 9 = 4 / (2 - f (3 * k + 2) 9) := by
        specialize hfn (3 * k + 2) 9 (by
          have h10 : (4 : ℝ) ≤ 9 := by norm_num
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
        )
        simpa using hfn
      have h12 : f (3 * k + 2) 9 = 4 / (2 - f (3 * k + 1) 9) := by
        specialize hfn (3 * k + 1) 9 (by
          have h10 : (4 : ℝ) ≤ 9 := by norm_num
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
        )
        simpa using hfn
      rw [h10, h11, h12, ih]
      field_simp
      <;> ring_nf <;> norm_num
  have h6 : 2023 = 3 * 674 + 1 := by
    omega
  rw [h6]
  apply h5 674
  all_goals norm_num