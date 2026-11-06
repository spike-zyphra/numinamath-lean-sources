import Mathlib

theorem algebra_97062 (x : ℕ) (h : 3^(2*x) + 9 = 10 * 3^x) :
    x^2 + 1 = 1 ∨ x^2 + 1 = 5 := by
  have h1 : 3 ^ (2 * x) = (3 ^ x) ^ 2 := by
    ring_nf
  rw [h1] at h 
  have h3 : (3 ^ x : ℕ) = 1 ∨ (3 ^ x : ℕ) = 9 := by
    have h3 : (3 ^ x : ℕ) ≤ 9 := by
      by_contra h3
      push_neg at h3
      have h4 : (3 ^ x : ℕ) ≥ 10 := by
        omega
      nlinarith [sq_nonneg ((3 ^ x : ℕ) : ℕ), sq_nonneg ((3 ^ x - 10 : ℤ)), sq_nonneg ((3 ^ x - 1 : ℤ)), sq_nonneg ((3 ^ x - 9 : ℤ)), 
        show (3 ^ x : ℕ) > 0 by positivity
      ]
    have h4 : (3 ^ x : ℕ) ≤ 9 := h3
    have h5 : (3 ^ x : ℕ) ≥ 1 := by
      have h2 : (3 ^ x : ℕ) ≥ 1 := by
        have h3 : ∀ (n : ℕ), (3 : ℕ) ^ n ≥ 1 := by
          intro n
          induction n with
          | zero => 
            norm_num
          | succ n ih => 
            simp [pow_succ] at ih ⊢
            all_goals omega
        specialize h3 x
        linarith
      linarith
    interval_cases (3 ^ x : ℕ) <;> omega
  rcases h3 with h3 | h3
  · -- Case 3^x = 1: so x=0
    have hx0 : x = 0 := by
      have h11 : (3 ^ x : ℕ) = 1 := h3
      have h22 : x = 0 := by
        have h33 : 3 ^ x = 1 := by
          omega
        have h44 : x = 0 := by
          exact Nat.pow_right_injective (by norm_num) h33
        exact h44
      exact_mod_cast h22
    left
    rw [hx0]
    all_goals norm_num
  · -- Case 3^x = 9: so x=2
    have hx2 : x = 2 := by
      have h11 : (3 ^ x : ℕ) = 9 := h3
      have h22 : x = 2 := by
        have h33 : 3 ^ x = 9 := by
          omega
        have h44 : x = 2 := by
          exact Nat.pow_right_injective (by norm_num) h33
        exact h44
      exact_mod_cast h22
    right
    rw [hx2]
    all_goals norm_num