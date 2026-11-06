import Mathlib

theorem algebra_310238 {f : ℝ → ℝ} (hπ4 : f (Real.pi / 4) = 0)
    (hf : ∀ x y, f x + f y = 2 * f ((x + y) / 2) * f ((x - y) / 2)) :
    ∑ i ∈ Finset.range 1004, f ((2 * i + 1) * Real.pi / 4) = 0 := by 
  have h0 : ∀ (n : ℕ), f ((2 * ((n : ℝ)) + 1) * Real.pi / 4) = 0 := by
    intro n
    induction' n with k ihk
    · norm_num
      norm_num at hπ4 ⊢
      linarith [hπ4]
    · have h1 : f ((2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.pi / 4) = 0 := by
        have h2 : (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.pi / 4 = (2 * ((k : ℝ) + 1) + 1) * Real.pi / 4 := by 
          simp at *
          <;> ring_nf
          <;> simp
          <;> ring
        rw [h2]
        have h3 : f ((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4) + f ((2 * (k : ℝ) + 1) * Real.pi / 4) = 
          2 * f (((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4 + (2 * (k : ℝ) + 1) * Real.pi / 4) / 2) * 
          f (((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4 - (2 * (k : ℝ) + 1) * Real.pi / 4) / 2) := by 
          apply hf 
        have h5 : (((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4 + (2 * (k : ℝ) + 1) * Real.pi / 4) / 2) = (k + 1 : ℝ) * Real.pi / 2 := by 
          ring_nf 
          <;> field_simp [Real.pi_pos]
          <;> ring 
        have h6 : (((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4 - (2 * (k : ℝ) + 1) * Real.pi / 4) / 2) = Real.pi / 4 := by 
          ring_nf 
          <;> field_simp [Real.pi_pos]
          <;> ring 
        have h4 : f ((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4) + f ((2 * (k : ℝ) + 1) * Real.pi / 4) = 
          2 * f ((k + 1 : ℝ) * Real.pi / 2) * f (Real.pi / 4) := by 
          rw [h5, h6] at h3 
          linarith 
        have h9 : f ((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4) + f ((2 * (k : ℝ) + 1) * Real.pi / 4) = 0 := by 
          rw [show f (Real.pi / 4) = 0 by linarith [hπ4]] at h4 
          linarith 
        have h7 : f ((2 * (k : ℝ) + 1) * Real.pi / 4) = 0 := by 
          exact_mod_cast ihk 
        have h8 : f ((2 * ((k : ℝ) + 1) + 1) * Real.pi / 4) = 0 := by 
          linarith [h7, h9] 
        exact_mod_cast h8 
      exact h1 
  simp [Finset.sum_eq_zero, h0]
  <;> try { 
    linarith [hπ4] 
    <;> ring_nf <;> linarith 
  }
  <;> try { 
    linarith 
  }
  all_goals 
  try { 
    linarith [Real.pi_pos] 
  }
  <;> try { 
    linarith 
  }