import Mathlib

open Real

theorem algebra_215285 {a : ℕ → ℝ} (ha0 : a 0 = 1) (han : ∀ n, a (n + 1) = sin (a n)) :
    Bornology.IsBounded {x | ∃ n, (a n)^2 = x} := by
  have h1 : ∀ n, 0 ≤ a n ∧ a n ≤ Real.pi := by 
    intro n
    induction n with
    | zero =>
      rw [ha0]
      constructor
      · norm_num
      · -- Show 1 ≤ π
        linarith [Real.pi_gt_three]
    | succ k ih =>
      have h4 : a (k + 1) = sin (a k) := han k
      have h9 : 0 ≤ a k := ih.1
      have h10 : a k ≤ Real.pi := ih.2
      rw [h4]
      constructor
      · -- Show 0 ≤ sin (a k)
        have h11 : sin (a k) ≥ 0 := by 
          apply sin_nonneg_of_nonneg_of_le_pi
          all_goals
            try linarith
        linarith
      · -- Show sin (a k) ≤ Real.pi
        have h12 : sin (a k) ≤ Real.pi := by
          have h13 : sin (a k) ≤ 1 := by
            apply sin_le_one
          have h14 : (1 : ℝ) < Real.pi := by
            linarith [Real.pi_gt_three]
          linarith
        linarith
  have h5 : ∀ n, a n ≤ 1 := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      all_goals norm_num
    | succ k ih =>
      have h4 : a (k + 1) = sin (a k) := han k
      rw [h4]
      have h6 : sin (a k) ≤ (1 : ℝ) := by
        apply sin_le_one
      linarith [h6, ih]
  have h6 : ∀ n, a n ≥ 0 := by
    intro n 
    exact (h1 n).1
  have h7 : ∀ n, (a n) ^ 2 ≤ 1 := by 
    intro n 
    have h8 : a n ≥ 0 := h6 n
    have h9 : a n ≤ 1 := h5 n
    nlinarith [sq_nonneg (a n)]
  -- Prove that the set {x | ∃ n, (a n) ^ 2 = x} is bounded
  have h8 : Bornology.IsBounded {x | ∃ n, (a n)^2 = x} := by
    have h9 : {x | ∃ n, (a n)^2 = x} ⊆ (Set.Icc (0 : ℝ) (1 : ℝ)) := by
      intro x hx
      rcases hx with ⟨n, hn⟩
      have hx1 : x ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
        have h100 : (a n) ^ 2 ≥ 0 := by nlinarith [h6 n, sq_nonneg (a n)]
        have h101 : (a n) ^ 2 ≤ 1 := h7 n
        have h10 : x ≥ 0 := by
          nlinarith [show (a n) ^ 2 = x from by linarith [hn]]
        have h11 : x ≤ 1 := by
          nlinarith [show (a n) ^ 2 = x from by linarith [hn]]
        exact ⟨h10, h11⟩
      exact hx1
    have h11 : Bornology.IsBounded (Set.Icc (0 : ℝ) (1 : ℝ)) := by
      apply IsCompact.isBounded
      exact isCompact_Icc
    apply Bornology.IsBounded.subset h11 h9
  exact h8