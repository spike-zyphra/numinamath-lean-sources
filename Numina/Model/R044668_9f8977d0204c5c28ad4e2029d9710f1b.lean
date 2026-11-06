import Mathlib

theorem algebra_155546 {u : ℕ → ℝ} (hu1 : u 1 = 5)
    (hun : ∀ n ≥ 1, u (n + 1) = u n + (2 * n + 5)) :
    (∀ n ≥ 1, u n = n ^ 2 + 4 * n) ∧
    (∀ n ≥ 1, (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) / n ≥ (n + 4) ^ 2) := by

  have h1 : ∀ n ≥ 1, u n = n ^ 2 + 4 * n := by
    intro n hn
    have h2 : ∀ n, n ≥ 1 → u n = n ^ 2 + 4 * n := by 
      intro n hn
      induction n with 
      | zero =>
        exfalso
        linarith 
      | succ k ih =>
        cases k with
        | zero => 
          rw [hu1]
          norm_num
        | succ k =>
          have h3 := ih (by linarith)
          simp [hun (k + 1) (by linarith)] at *
          rw [h3]
          ring_nf 
    specialize h2 n hn 
    simpa using h2

  have h2 : ∀ n ≥ 1, (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) / n ≥ (n + 4) ^ 2 := by 
    intro n hn
    have h3 : (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) = 4 * (n : ℝ) ^ 3 / 3 + 8 * (n : ℝ) ^ 2 + 47 * (n : ℝ) / 3 := by
      have h4 : ∀ (n : ℕ), (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) = 4 * (n : ℝ) ^ 3 / 3 + 8 * (n : ℝ) ^ 2 + 47 * (n : ℝ) / 3 := by
        intro n
        induction n with 
        | zero =>
          simp 
        | succ n ih => 
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          field_simp at *
          ring 
      specialize h4 n 
      simpa using h4

    have h7 : (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) / (n : ℝ) = (4 * (n : ℝ) ^ 2 + 24 * (n : ℝ) + 47 ) / 3 := by
      have h8 : (n : ℝ) ≠ 0 := by 
        have h9 : (n : ℝ) ≥ (1 : ℝ) := by 
          exact_mod_cast (show n ≥ 1 by omega)
        nlinarith 
      rw [h3]
      field_simp 
      ring
    rw [h7]

    have h8 : (4 * (n : ℝ) ^ 2 + 24 * (n : ℝ) + 47 ) / 3 ≥ (n + 4) ^ 2 := by 
      have h9 : (n : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast hn 
      have h10 : (4 * (n : ℝ) ^ 2 + 24 * (n : ℝ) + 47 ) ≥ 3 * ((n + 4) ^ 2) := by 
        have h11 : (n : ℝ) ≥ 1 := h9
        have h12 : (n : ℝ) ^ 2 ≥ 1 := by nlinarith 
        nlinarith 
      apply (le_div_iff₀ (by norm_num)).mpr 
      linarith 
    linarith
  constructor 
  · exact h1 
  · intro n hn 
    specialize h2 n hn 
    simpa using h2