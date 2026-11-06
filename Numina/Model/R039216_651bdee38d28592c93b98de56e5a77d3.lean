import Mathlib

theorem algebra_10998 {a b : ℕ → ℝ} (h : ∀ k ≥ 1, a k * b k = 1)
    (h' : ∀ n, ∑ i ∈ Finset.Icc 1 n, a i = n / (n + 1)) :
    ∀ n, ∑ i ∈ Finset.Icc 1 n, b i = n * (n + 1) * (n + 2) / 3 := by

  intro n

  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, a i = n / (n + 1) := by
    intro n
    specialize h' n
    simpa using h'

  have h5 : ∀ n : ℕ, b (n + 1) = (n + 1) * (n + 2 : ℝ) := by 
    intro n
    have eq1 : a (n + 1) * b (n + 1) = 1 := h (n + 1) (by linarith)
    have eq2 : a (n + 1) = 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
      have eq3 : (∑ i ∈ Finset.Icc 1 (n + 1), a i) = (↑(n + 1) / (↑(n + 1) + 1 : ℝ)) := by 
        specialize h1 (n + 1)
        simpa using h1
      have eq4 : (∑ i ∈ Finset.Icc 1 (n : ℕ), a i) = (↑n / (↑n + 1 : ℝ)) := by 
        specialize h1 (n)
        simpa using h1
      have eq5 : (∑ i ∈ Finset.Icc 1 (n + 1 : ℕ), a i) = (∑ i ∈ Finset.Icc 1 (n : ℕ), a i) + a (n + 1 : ℕ) := by 
        rw [Finset.sum_Icc_succ_top]
        all_goals linarith
      rw [eq5] at eq3
      rw [eq4] at eq3
      have eq6 : a (n + 1 : ℕ) = (1 : ℝ) / ( ( (↑n + 1 : ℝ) ) * ( (↑n + 2 : ℝ) ) ) := by 
        field_simp at eq3 ⊢
        ring_nf at eq3 ⊢
        nlinarith 
      have eq7 : a (n + 1 : ℕ) = (1 : ℝ) / ( ( (n + 1 : ℝ ) ) * ( (n + 2 : ℝ ) ) ) := by 
        simpa [show (↑n + 1 : ℝ) = (n + 1 : ℝ) by simp] using eq6
      simpa using eq7 
    rw [eq2] at eq1
    have eq8 : b (n + 1) = ( (n + 1 : ℝ ) * ( (n + 2 : ℝ ) ) ) := by 
      field_simp at eq1 ⊢
      nlinarith 
    simpa using eq8 
  have h6 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, b i = n * (n + 1) * (n + 2) / 3 := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have eq1 : b (n + 1) = ( (n + 1 : ℝ ) * ( (n + 2 : ℝ ) ) ) := by 
        specialize h5 n 
        simpa using h5 
      simp [eq1]
      field_simp at *
      nlinarith 
  specialize h6 n 
  simpa using h6