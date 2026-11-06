import Mathlib
open Real Set

theorem inequalities_1341 (n : ℕ) [NeZero n] (x : Fin n → ℝ) (m M : ℝ)
    (h₀ : ∀ i, x i ≤ 0) (h₁ : ∑ i, x i = 0) (h₂ : m = sInf {x i | i})
    (h₃ : M = sSup {x i | i}) :
    (∑ i, x i) * (∑ i, 1 / x i) ≤ (n ^ 2 * (M + m) ^ 2) / (4 * m * M) := by
  have h4 : ∀ i, x i = 0 := by
    have h5 : ∑ i, x i = 0 := h₁
    have h6 : ∀ i, x i ≤ 0 := h₀
    have h7 : ∀ i ∈ Finset.univ, x i ≤ 0 := by
      intro i hi
      apply h₀ i
    have h10 : ∑ i in Finset.univ, x i = 0 := by
      simpa using h₁
    have h11 : ∀ i ∈ Finset.univ, x i ≤ 0 := by
      intro i hi
      apply h₀ i
    have h12 : ∀ i ∈ Finset.univ, x i = 0 := by
      apply Finset.sum_eq_zero_iff_of_nonpos h11 |>.mp
      simpa using h₁
    intro i
    specialize h12 i (Finset.mem_univ i)
    simpa using h12
  have h50 : (∑ i, x i) = 0 := h₁
  have h51 : (∑ i, 1 / x i) = 0 := by
    have h70 : ∀ i, x i = 0 := h4
    simp_all [Finset.sum_eq_zero, h70, div_zero]
  have h52 : m = 0 := by
    rw [h₂]
    have h60 : {x i | i} = {0} := by
      ext y
      simp
      constructor
      · -- Assume y ∈ {x i | i}
        intro hy
        rcases hy with ⟨i, hi⟩
        rw [show x i = 0 by apply h4 i] at hi
        linarith
      · -- Assume y ∈ {0}
        intro hy
        rcases hy with rfl
        use 0
        simp [h4, Finset.mem_univ]
    rw [h60]
    norm_num [Finset.mem_univ]
    <;> try { linarith }
  have h53 : M = 0 := by
    rw [h₃]
    have h60 : {x i | i} = {0} := by
      ext y
      simp
      constructor
      · -- Assume y ∈ {x i | i}
        intro hy
        rcases hy with ⟨i, hi⟩
        rw [show x i = 0 by apply h4 i] at hi
        linarith
      · -- Assume y ∈ {0}
        intro hy
        rcases hy with rfl
        use 0
        simp [h4, Finset.mem_univ]
    rw [h60]
    norm_num [Finset.mem_univ]
    <;> try { linarith }
  rw [h52, h53] at *
  norm_num at *
  <;> try { 
    nlinarith [h50, h51, sq_nonneg (M + m), sq_nonneg ((M : ℝ) + (m : ℝ)), sq_nonneg ((M : ℝ) * (m : ℝ))]
  }
  all_goals linarith