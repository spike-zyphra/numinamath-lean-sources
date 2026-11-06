import Mathlib

open scoped BigOperators

theorem algebra_103815 (a : ℕ → ℝ) (ha0 : a 0 = 1)
  (hak : ∀ k, a (k + 1) = a k + 1 / a k) : a 2021 > 60 := by
  have h1 : ∀ k, a k > 0 := by 
    intro k 
    induction k with 
    | zero => 
      rw [ha0]
      norm_num 
    | succ k ih =>
      have h2 : a (k + 1) = a k + 1 / a k := hak k 
      rw [h2] 
      have h20 : a k > 0 := ih 
      have h21 : 1 / a k > 0 := by 
        apply div_pos 
        norm_num 
        all_goals linarith [h20] 
      positivity 
  have h9 : ∀ k : ℕ, a k ≥ Real.sqrt (2 * (k : ℝ) + 1) := by 
    intro k 
    induction k with 
    | zero => 
      rw [ha0] 
      have h114 : Real.sqrt (2 * (0 : ℝ) + 1) = (1 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      norm_num [h114]
    | succ k ih =>
      have h8 : a (k + 1) = a k + 1 / a k := hak k 
      rw [h8] 
      have h91 : a k ≥ 0 := by 
        have h60 : a k > 0 := h1 k 
        linarith [h60]
      have h12 : a k ≥ Real.sqrt (2 * (k : ℝ) + 1) :=ih 
      have h61 : (a k + 1 / a k) ^ 2 ≥ (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) := by 
        have h11 : a k ^ 2 ≥ (2 * (k : ℝ) + 1 : ℝ) := by 
          have h13 : (Real.sqrt (2 * (k : ℝ) + 1)) ^ 2 = (2 * (k : ℝ) + 1 : ℝ) := by 
            apply Real.sq_sqrt 
            positivity 
          have h14 : a k ≥ Real.sqrt (2 * (k : ℝ) + 1) := h12 
          nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1)]
        have h10 : a k > 0 := h1 k 
        have eq2 : (a k + 1 / a k) ^ 2 = a k ^ 2 + 2 + 1 / (a k ^ 2) := by 
          field_simp [h10]
          <;> ring 
        have eq3 : a k ^ 2 + 2 + 1 / (a k ^ 2) ≥ (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) := by 
          have eq4 : (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) = (2 * (k : ℝ) + 3 : ℝ) := by 
            simp at *
            all_goals ring_nf 
          rw [eq4]
          have h10 : a k ^ 2 ≥ (2 * (k : ℝ) + 1 : ℝ) := h11 
          have h9 : a k ^ 2 > 0 := by 
            have h104 : a k > 0 := h1 k 
            nlinarith [h104]
          have h40 : 1 / (a k ^ 2) > 0 := by 
            positivity 
          nlinarith [sq_nonneg (a k ^ 2 - 1), sq_nonneg (a k ^ 2 - 2)]
        linarith [eq2, eq3] 
      have h90 : a k + 1 / a k ≥ Real.sqrt (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) := by 
        have h71 : (a k + 1 / a k : ℝ) ≥ 0 := by 
          have h76 : a k > 0 := h1 k 
          have h26 : a k + 1 / a k > 0 := by 
            have h57 : a k > 0 := h76 
            have h49 : 1 / a k > 0 := by 
              positivity 
            linarith [h49, h57]
          linarith
        have h72 : Real.sqrt (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) ≥ 0 := by 
          positivity 
        have eq5 : Real.sqrt (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) ^ 2 = (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ) := by 
          apply Real.sq_sqrt 
          positivity 
        nlinarith [Real.sqrt_nonneg (2 * (↑(k + 1 : ℕ) : ℝ) + 1 : ℝ)]
      linarith [h90] 
  have h70 : a 2021 ≥ Real.sqrt (2 * (2021 : ℝ) + 1) := by 
    specialize h9 2021 
    simpa using h9 
  have h600 : Real.sqrt (2 * (2021 : ℝ) + 1) > 60 := by
    have h7 : Real.sqrt (2 * (2021 : ℝ) + 1) > 60 := by 
      have h4043 : (2 * (2021 : ℝ) + 1 : ℝ) = (4043 : ℝ) := by 
        ring_nf 
      rw [h4043] 
      have h87595 : Real.sqrt (4043 : ℝ) > 60 := by 
        nlinarith [Real.sqrt_nonneg (4043 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4043 : ℝ) by norm_num)]
      linarith 
    linarith 
  have h00 : a 2021 > 0 := by 
    apply h1 2021 
  nlinarith [h70, h600, Real.sqrt_nonneg (2 * (2021 : ℝ) + 1)]