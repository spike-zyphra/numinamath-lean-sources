import Mathlib

theorem calculus_15686 (θ : ℝ) (h : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = 5) :
    Real.cos (2 * θ) = 3 / 5 := by
  have h1 : Real.cos θ ^ 2 < 1 := by
    by_contra h3
    push_neg at h3
    have h4 : Real.cos θ ^ 2 ≥ 1 := by linarith
    have h5 : Real.cos θ ^ 2 ≤ 1 := by
      have h8 : Real.cos θ ^ 2 ≤ 1 := by
        have h9 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
        have h10 : Real.cos θ ≤ 1 := Real.cos_le_one θ
        nlinarith [sq_nonneg (Real.cos θ - 1), sq_nonneg (Real.cos θ + 1)]
      linarith
    have h6 : Real.cos θ ^ 2 = 1 := by linarith
    have h7 : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = ∑' n : ℕ, (1 : ℝ) := by
      have h8 : ∀ n : ℕ, (Real.cos θ) ^ (2 * n) = (1 : ℝ) := by
        intro n
        have h9 : Real.cos θ ^ 2 = 1 := h6
        have h10 : (Real.cos θ) ^ (2 * n) = (Real.cos θ ^ 2) ^ n := by
          rw [← pow_mul]
          all_goals 
            ring_nf 
        rw [h10, h9]
        all_goals 
          simp 
      congr 
      funext n 
      exact h8 n
    rw [h7] at h
    norm_num at h 
  have h2 : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = 1 / (1 - Real.cos θ ^ 2) := by
    have h10 : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = ∑' n : ℕ, (Real.cos θ ^ 2) ^ n := by
      have h12 : ∀ n : ℕ, (Real.cos θ) ^ (2 * n) = (Real.cos θ ^ 2) ^ n := by
        intro n
        induction n with
        | zero => 
          simp
        | succ n ih => 
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals 
            nlinarith 
      have h13 : ∑' n : ℕ, (Real.cos θ) ^ (2 * n) = ∑' n : ℕ, (Real.cos θ ^ 2) ^ n := by
        congr 
        funext n 
        exact h12 n 
      exact h13 
    rw [h10] 
    rw [tsum_geometric_of_norm_lt_one] 
    · ring 
    · -- Show that |Real.cos θ ^ 2| < 1 
      have h42 : |Real.cos θ ^ 2| < 1 := by 
        rw [abs_of_nonneg (show 0 ≤ Real.cos θ ^ 2 by positivity)]
        linarith [h1] 
      exact h42 
  rw [h2] at h 
  have h3 : Real.cos θ ^ 2 = 4 / 5 := by 
    field_simp [(show (1 - Real.cos θ ^ 2 : ℝ) ≠ 0 by 
      nlinarith [sq_nonneg (Real.cos θ ^ 2 - 1), h1]
    )] at h 
    nlinarith [Real.cos_sq_add_sin_sq θ, h1] 
  have h4 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by 
    rw [Real.cos_two_mul] 
  rw [h4, h3] 
  all_goals 
    norm_num