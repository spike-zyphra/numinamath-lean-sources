import Mathlib

theorem algebra_166197 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b) (m n : ℕ) (hm : m > 2) (hn : n > 2)
    (hmn : m ≠ n) (hsum1 : ∑ i ∈ Finset.Icc 1 m, f i = -n) (hsum2 : ∑ i ∈ Finset.Icc 1 n, f i = -m) :
    (∑ i ∈ Finset.Icc 1 (m + n), f i) / (m + n) = 1 := by

  have eq1 : ∀ (i : ℕ), f i = a * (i : ℝ) + b := by
    intro i
    specialize hf i
    simpa using hf

  have sum_formula : ∀ (k : ℕ), ∑ i ∈ Finset.Icc 1 k, f i = a * ((k : ℝ) * (k + 1) / 2) + b * (k : ℝ) := by
    intro k
    induction k with
    | zero =>
      norm_num [Finset.sum_eq_zero]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [eq1]
      simp [ih]
      <;> ring_nf
      <;> field_simp
      <;> ring

  have h1 : ∑ i ∈ Finset.Icc 1 m, f i = a * ((m : ℝ) * (m + 1) / 2) + b * (m : ℝ) := by
    specialize sum_formula m
    simpa using sum_formula

  have h2 : ∑ i ∈ Finset.Icc 1 n, f i = a * ((n : ℝ) * (n + 1) / 2) + b * (n : ℝ) := by
    specialize sum_formula n
    simpa using sum_formula

  rw [h1] at hsum1
  rw [h2] at hsum2

  have sum_formula_m_n : ∑ i ∈ Finset.Icc 1 (m + n), f i = a * ((m + n : ℝ) * (m + n + 1) / 2) + b * (m + n : ℝ) := by
    specialize sum_formula (m + n)
    simpa using sum_formula

  have eq5 : a * (m * (m + 1 : ℝ)) + 2 * b * (m : ℝ) = -2 * (n : ℝ) := by
    have h : a * ((m : ℝ) * (m + 1) / 2) + b * (m : ℝ) = -(n : ℝ) := by linarith
    nlinarith

  have eq6 : a * (n * (n + 1 : ℝ)) + 2 * b * (n : ℝ) = -2 * (m : ℝ) := by
    have h : a * ((n : ℝ) * (n + 1) / 2) + b * (n : ℝ) = -(m : ℝ) := by linarith
    nlinarith

  have eq7 : a * (m * (m + 1 : ℝ)) + 2 * b * (m : ℝ) + 2 * (n : ℝ) = 0 := by
    linarith [eq5]

  have eq8 : a * (n * (n + 1 : ℝ)) + 2 * b * (n : ℝ) + 2 * (m : ℝ) = 0 := by
    linarith [eq6]

  have eq9 : (m : ℝ) - (n : ℝ) ≠ 0 := by
    by_contra h
    have : (m : ℝ) = (n : ℝ) := by linarith
    have hmn' : m = n := by
      exact_mod_cast this
    contradiction

  have eq10 : a * ((m + n + 1 : ℝ)) + 2 * b = 2 := by
    have eq5' : a * (m * (m + 1 : ℝ)) + 2 * b * (m : ℝ) + 2 * (n : ℝ) = 0 := eq7
    have eq6' : a * (n * (n + 1 : ℝ)) + 2 * b * (n : ℝ) + 2 * (m : ℝ) = 0 := eq8
    have h4 : (m : ℝ) - (n : ℝ) ≠ 0 := eq9
    have h5 : a * ((m * (m + 1 : ℝ)) - (n * (n + 1 : ℝ))) + 2 * b * ((m : ℝ) - (n : ℝ)) + 2 * ((n : ℝ) - (m : ℝ)) = 0 := by
      nlinarith
    have h6 : a * ((m * (m + 1 : ℝ)) - (n * (n + 1 : ℝ))) = a * ((m : ℝ) - (n : ℝ)) * (m + n + 1 : ℝ) := by
      ring
    rw [h6] at h5
    have h7 : a * ((m : ℝ) - (n : ℝ)) * (m + n + 1 : ℝ) + 2 * b * ((m : ℝ) - (n : ℝ)) + 2 * ((n : ℝ) - (m : ℝ)) = 0 := by
      linarith
    have h8 : ((m : ℝ) - (n : ℝ)) * (a * (m + n + 1 : ℝ) + 2 * b - 2) = 0 := by
      ring_nf at h7 ⊢
      linarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Assume (m : ℝ) - (n : ℝ) = 0
      exfalso
      apply eq9
      linarith
    · -- Assume a * (m + n + 1 : ℝ) + 2 * b - 2 = 0
      linarith

  rw [sum_formula_m_n]
  have m_plus_n_card : (m + n : ℝ) ≠ 0 := by
    have hm' : (m : ℝ) > (2 : ℝ) := by exact_mod_cast hm
    have hn' : (n : ℝ) > (2 : ℝ) := by exact_mod_cast hn
    nlinarith
  field_simp at *
  nlinarith [eq10]