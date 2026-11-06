import Mathlib

theorem algebra_84611 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y)
    (h' : f 1 = 100) :
    ∑ k in Finset.Icc 1 10, f (Nat.factorial k) = 403791300 := by
  have h1 : ∀ n : ℕ, f (↑n) = 100 * (↑n : ℝ) := by
    intro n 
    induction n with
    | zero =>
      have h2 : f (0 : ℝ) = 0 := by
        have h1 : f (0 + 0) = f (0) + f (0) := h 0 0
        simp at h1 
        linarith 
      simp [h2]
    | succ n ih =>
      have h2 : f (↑(n + 1 : ℕ) : ℝ) = f (↑n : ℝ) + f (1 : ℝ) := by
        rw [show ↑(n + 1 : ℕ) = (↑n : ℝ) + (1 : ℝ) by simp]
        apply h 
      rw [h2]
      rw [ih]
      rw [h']
      simp [add_mul, mul_add]
  have h2 : ∀ k : ℕ, f (Nat.factorial k : ℝ) = 100 * (Nat.factorial k : ℝ) := by
    intro k
    specialize h1 (Nat.factorial k)
    simpa using h1
  have h3 : ∑ k in Finset.Icc 1 10, f (Nat.factorial k : ℝ) = 
    403791300 := by 
    have h4 : ∀ k ∈ Finset.Icc 1 10, f (Nat.factorial k : ℝ) = 100 * (Nat.factorial k : ℝ) := by
      intro k hk
      specialize h2 k 
      simpa using h2
    have h5 : ∑ k in Finset.Icc 1 10, f (Nat.factorial k : ℝ) = 
      ∑ k in Finset.Icc 1 10, (100 * (Nat.factorial k : ℝ)) := by 
      apply Finset.sum_congr
      · rfl
      · intro k hk
        exact h4 k hk 
    rw [h5]
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
  exact h3