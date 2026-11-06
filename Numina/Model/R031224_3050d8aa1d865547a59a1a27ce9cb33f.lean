import Mathlib

theorem algebra_179477 (n : ℕ) (h : n ≤ 25) (p : ℕ → ℝ)
    (hp : ∀ i, p i = if i = 0 then 1 else p (i - 1) + 0.5) :
    ∑ i ∈ Finset.range (25 - n), p i = 7 ↔ n = 21 := by
  have eq1 : ∀ k : ℕ, p k = 1 + 0.5 * (↑k : ℝ) := by
    intro k
    induction k with
    | zero =>
      have h1 : p 0 = 1 := by
        specialize hp 0
        norm_num at hp ⊢
        all_goals try { linarith }
      simp [h1]
    | succ k ih =>
      have h2 : p (k + 1) = p k + 0.5 := by
        specialize hp (k + 1)
        simp [show k + 1 ≠ 0 by omega] at hp ⊢
        all_goals
          linarith
      rw [h2, ih]
      simp [add_assoc] at *
      all_goals ring_nf
  have eq2 : ∀ (m : ℕ), ∑ i in Finset.range m, p i = (↑m : ℝ) * (↑m + 3) / 4 := by
    intro m
    induction m with
    | zero =>
      norm_num [Finset.sum_range_succ, eq1]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have eq3 : p m = 1 + 0.5 * (↑m : ℝ) := eq1 m
      simp [eq3]
      field_simp at *
      ring_nf at *
  constructor
  · -- Assume the total is 7.
    intro h_eq
    have eq3 : ∑ i ∈ Finset.range (25 - n), p i = (↑(25 - n) : ℝ) * (↑(25 - n) + 3) / 4 := by
      apply eq2 (25 - n)
    rw [eq3] at h_eq
    have eq4 : (↑(25 - n) : ℝ) * (↑(25 - n) + 3) / 4 = 7 := by
      linarith
    have eq5 : (↑(25 - n) : ℝ) * (↑(25 - n) + 3) = 28 := by
      linarith
    have eq7 : (↑(25 - n) : ℝ) = (4 : ℝ) := by
      have h1 : (↑(25 - n) : ℝ) ≤ (25 : ℝ) := by
        have h10 : (25 - n : ℕ) ≤ 25 := by
          omega
        have h11 : (↑(25 - n) : ℝ) ≤ (25 : ℝ) := by
          exact_mod_cast h10
        nlinarith
      nlinarith [sq_nonneg ((↑(25 - n) : ℝ) - 4 : ℝ), sq_nonneg ((↑n : ℝ) - (21 : ℝ))]
    have eq9 : (25 - n : ℕ) = 4 := by
      exact_mod_cast eq7
    have eq10 : n = 21 := by
      omega
    exact eq10
  · -- Assume n = 21.
    intro h_eq
    rw [h_eq] at *
    have eq3 : ∑ i ∈ Finset.range (25 - (21 : ℕ)), p i = (↑(25 - (21 : ℕ)) : ℝ) * (↑(25 - (21 : ℕ)) + 3) / 4 := by
      apply eq2 (25 - (21 : ℕ))
    rw [eq3]
    norm_num