import Mathlib

open Real

theorem inequalities_151407 (n : ℕ) (hn : 1 ≤ n) :
    1 - 1 / n < ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1)) ∧
    ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1)) < 1 := by
  have h1 : 1 ≤ n := hn
  have hn1 : n ≥ 1 := h1
  have hn2 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by linarith)
  constructor
  · -- Prove the lower bound: 1 - 1 / n < ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1))
    have h8 : ∀ i : ℕ, i ∈ Finset.range n → (1 / sqrt (n ^ 2 + (i : ℝ) + 1) > 1 / ((n + 1 : ℝ))) := by
      intro i hi
      have h2' : i < n := Finset.mem_range.mp hi
      have hn1 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by linarith)
      have h7 : (n + 1 : ℝ) > 0 := by linarith
      have h8 : (n ^ 2 + (i : ℝ) + 1) < (n + 1 : ℝ) ^ 2 := by
        have h9 : (i : ℝ) < (n : ℝ) := by exact_mod_cast (show i < n by linarith)
        nlinarith
      have h10 : sqrt (n ^ 2 + (i : ℝ) + 1) < sqrt ((n + 1 : ℝ) ^ 2) := by
        apply Real.sqrt_lt_sqrt
        nlinarith
        nlinarith
      have h11 : sqrt ((n + 1 : ℝ) ^ 2) = (n + 1 : ℝ) := by
        rw [Real.sqrt_sq]
        nlinarith
      have h12 : sqrt (n ^ 2 + (i : ℝ) + 1) < (n + 1 : ℝ) := by
        linarith [h11, h10]
      have h3 : (1 / sqrt (n ^ 2 + (i : ℝ) + 1) : ℝ) > 1 / (n + 1 : ℝ) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [show sqrt (n ^ 2 + (i : ℝ) + 1) > 0 by positivity, h12]
      simpa using h3
    have h13 : ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1) : ℝ) > ∑ i ∈ Finset.range n, (1 / ((n + 1 : ℝ) ) ) := by
      apply Finset.sum_lt_sum
      · -- Show 1 / sqrt (n ^ 2 + i + 1) ≥ 1 / ((n + 1 : ℝ) ) for all i in Finset.range n
        intro i hi
        specialize h8 i hi
        linarith
      · -- Show there exists i such that `1 / sqrt (n ^ 2 + i + 1) > 1 / (n + 1 : ℝ) ` 
        use 0
        constructor
        · -- Show 0 ∈ Finset.range n
          simp
          all_goals linarith
        · -- Show 1 / sqrt (n ^ 2 + 0 + 1) > 1 / (n + 1 : ℝ)
          specialize h8 0 (by simp; all_goals linarith)
          simpa using h8
    have h14 : ∑ i ∈ Finset.range n, (1 / ((n + 1 : ℝ) ) ) = (n : ℝ) / (n + 1 : ℝ) := by
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> field_simp
      <;> linarith
    have h16 : ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1) : ℝ) > (n : ℝ) / (n + 1 : ℝ) := by
      linarith [h14, h13]
    have hn' : (1 - (1 / (n : ℝ)) ) < (n / (n + 1) ) := by
      have n1 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by linarith
      have n1' : (n + 1 : ℝ) > 0 := by linarith
      rw [show 1 - 1 / (n : ℝ) = ((n: ℝ) - 1) / (n: ℝ) by field_simp, show (n / (n + 1) ) = (n: ℝ) / (n + 1: ℝ) by rfl]
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [show (n : ℝ) ≥ 1 by linarith, sq_nonneg ((n: ℝ) - 1) ]
    linarith [h16, hn']
  · -- Prove the upper bound: ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1)) < 1
    have h3 : ∀ i : ℕ, i ∈ Finset.range n → 1 / sqrt (n ^ 2 + i + 1) < 1 / (n : ℝ) := by
      intro i hi
      have h1' : i < n := Finset.mem_range.mp hi
      have h4 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by linarith)
      have h5 : (n ^ 2 + (i : ℝ) + 1) > (n : ℝ) ^ 2 := by
        have h6 : (i : ℝ) ≥ 0 := by exact_mod_cast (show i ≥ 0 by omega)
        nlinarith
      have h7 : sqrt (n ^ 2 + (i : ℝ) + 1) > sqrt ((n : ℝ) ^ 2) := by
        apply Real.sqrt_lt_sqrt
        nlinarith
        nlinarith
      have h8 : sqrt ((n : ℝ) ^ 2) = (n : ℝ) := by
        rw [Real.sqrt_sq]
        nlinarith
      have h9 : sqrt (n ^ 2 + (i : ℝ) + 1) > (n : ℝ) := by
        rw [h8] at h7
        linarith
      have h10 : (1 / sqrt (n ^ 2 + (i : ℝ) + 1) : ℝ) < (1 / (n : ℝ)) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [show sqrt (n ^ 2 + (i : ℝ) + 1) > (n : ℝ) by linarith [h9]]
      simpa using h10
    have h13 : ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1) : ℝ) < ∑ i ∈ Finset.range n, (1 / (n : ℝ) ) := by
      apply Finset.sum_lt_sum
      · -- Show that 1 / sqrt (n ^ 2 + i + 1) ≤ 1 / (n : ℝ) for all i in Finset.range n
        intro i hi
        specialize h3 i hi
        linarith
      · -- Show that 1 / sqrt (n ^ 2 + 0 + 1) < 1 / (n : ℝ)
        use 0
        constructor
        · -- Show 0 ∈ Finset.range n
          simp
          all_goals linarith
        · -- Show 1 / sqrt (n ^ 2 + (0 : ℝ) + 1) < 1 / (n : ℝ)
          specialize h3 0 (by simp; all_goals linarith)
          simpa using h3
    have h5 : ∑ i ∈ Finset.range n, (1 / (n : ℝ) ) = (n : ℝ) / (n : ℝ) := by
      have hn' : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by linarith
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> field_simp [hn']
      <;> linarith
    have h6 : ∑ i ∈ Finset.range n, (1 / sqrt (n ^ 2 + i + 1) : ℝ) < 1 := by
      rw [h5] at h13
      have hn' : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by linarith
      have h7 : (n : ℝ) / (n : ℝ) = 1 := by
        field_simp [hn']
      linarith [h7, h13]
    exact_mod_cast h6