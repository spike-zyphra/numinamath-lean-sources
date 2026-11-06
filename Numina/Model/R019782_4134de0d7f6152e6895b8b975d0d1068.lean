import Mathlib

theorem algebra_278848 {f : ℝ → ℝ} (h : ∀ a b, f (a + b) = f a * f b) (h1 : f 1 = 1) :
    ∑ i ∈ Finset.range 1987, f (i + 2) / f (i + 1) = 1987 := by 
  have h2 : ∀ (n : ℕ), f ((↑n : ℝ)) = 1 := by 
    intro n 
    induction n with 
    | zero => 
      have h3 : f (0 : ℝ) = 1 := by 
        have h0 : f (0 : ℝ) = f (0 : ℝ) * f (0 : ℝ) := by 
          specialize h (0 : ℝ) (0 : ℝ)
          norm_num at h ⊢ 
          linarith 
        have h4 : f (0 : ℝ) * (f (0 : ℝ) - 1) = 0 := by 
          linarith 
        cases' (mul_eq_zero.1 h4) with h5 h6 
        · -- Show a contradiction if f 0 = 0 
          exfalso 
          have h7 : f (1 : ℝ) = 0 := by 
            specialize h (1 : ℝ) (0 : ℝ)
            rw [show (1 : ℝ) + (0 : ℝ) = (1 : ℝ) by ring] at h
            rw [h5] at h 
            linarith 
          linarith [h1, h7]
        · -- f 0 = 1 
          linarith 
      simpa using h3 
    | succ n ih =>
      have h5 : f (↑(n + 1 : ℕ) : ℝ) = f (↑n : ℝ) * f (1 : ℝ) := by 
        specialize h (↑n : ℝ) (1 : ℝ)
        have h6 : (↑n : ℝ) + (1 : ℝ) = (↑(n + 1 : ℕ) : ℝ) := by 
          simp at *
          <;> ring 
        rw [h6] at h 
        linarith 
      rw [h5] 
      rw [ih]
      rw [h1]
      all_goals norm_num 
  have hterm : ∀ i ∈ Finset.range 1987, f (↑i + 2) / f (↑i + 1) = 1 := by 
    intro i hi 
    have h6 : f (↑i + 2 : ℝ) = 1 := by
      have h7 : f (↑(i + 2 : ℕ) : ℝ) = 1 := h2 (i + 2)
      rw [show (↑i + 2 : ℝ) = (↑(i + 2 : ℕ) : ℝ) by 
        simp [Nat.cast_add, Nat.cast_ofNat]
      ] at *
      linarith [h7]
    have h7 : f (↑i + 1 : ℝ) = 1 := by
      have h7_cast : f (↑(i + 1 : ℕ) : ℝ) = 1 := h2 (i + 1)
      rw [show (↑i + 1 : ℝ) = (↑(i + 1 : ℕ) : ℝ) by 
        simp [Nat.cast_add, Nat.cast_ofNat]
      ] at *
      linarith [h7_cast]
    rw [h6, h7]
    norm_num
  have h5 : ∑ i in Finset.range 1987, f (↑i + 2) / f (↑i + 1) = 1987 := by 
    have h6 : ∑ i in Finset.range 1987, f (↑i + 2) / f (↑i + 1) = ∑ i in Finset.range 1987, (1 : ℝ) := by 
      apply Finset.sum_congr 
      · rfl
      · intro i hi 
        exact hterm i hi 
    rw [h6]
    simp 
    <;> norm_num 
  exact_mod_cast h5