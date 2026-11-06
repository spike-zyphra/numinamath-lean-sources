import Mathlib
theorem number_theory_611268 : {x : ℤ | x ∈ Finset.Icc 1 2004 ∧ ∃ m n : ℤ, m > 0 ∧ n > 0 ∧ ((↑x : ℝ) = (m * n + 1) / (m + n))}.ncard = 2004:= by
  have h1 : {x : ℤ | x ∈ Finset.Icc 1 2004 ∧ ∃ m n : ℤ, m > 0 ∧ n > 0 ∧ ((↑x : ℝ) = (m * n + 1) / (m + n))} = Set.Icc (1 : ℤ) 2004 := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Forward implication 
      rintro ⟨⟨hx1, hx2⟩, ⟨m, n, hm, hn, h⟩⟩
      constructor
      · linarith
      · linarith
    · -- Backward implication
      rintro ⟨hx1, hx2⟩
      constructor
      · -- Show that x in the interval [1, 2004]
        constructor
        · linarith
        · linarith
      · -- Show existence of positive integers m, n
        use x + 1, x ^ 2 + x - 1
        constructor
        · -- Show that m > 0
          nlinarith 
        constructor
        · -- Show that n > 0
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (x + 1 : ℤ)]
        · -- Verify the equation
          have h3_eq : (↑x : ℝ) = ( ( (x + 1 : ℝ) ) * ( (x ^ 2 + x - 1 : ℝ) ) + 1 ) / ( (x + 1 : ℝ) + (x ^ 2 + x - 1 : ℝ) ) := by
            have eq1 : ( (x + 1 : ℝ) ) * ( (x ^ 2 + x - 1 : ℝ) ) + 1 = (x : ℝ) * ( (x + 1 : ℝ) + (x ^ 2 + x - 1 : ℝ) ) := by ring
            have h4 : ( (x + 1 : ℝ) + (x ^ 2 + x - 1 : ℝ) ) ≠ 0 := by
              have h5 : (x : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (x : ℤ) ≥ 1 by linarith)
              nlinarith [sq_nonneg ((x : ℝ) + 1), sq_nonneg ((x : ℝ) ), sq_nonneg ( (x ^ 2 + (x : ℝ) - 1 ) ) ]
            field_simp [h4] at eq1 ⊢ 
            <;> linarith
          rw [h3_eq]
          <;> norm_num
          <;> ring_nf <;> norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp