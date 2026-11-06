import Mathlib

theorem algebra_248950 {a : ℕ → ℝ} (h : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha : a 0 + a 2 = 20) (hb : a 1 + a 3 = 40) (hS : ∑ i in Finset.range n, a i = 1020) :
    n = 8 := by 
  rcases h with ⟨r, hr⟩
  have ha2 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr
  have ha1 : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    simpa using hr
  have ha3 : a 3 = a 0 * r ^ 3 := by
    specialize hr 3
    simpa using hr
  rw [ha2] at ha
  rw [ha1, ha3] at hb
  have eq1 : a 0 * (1 + r ^ 2) = 20 := by
    nlinarith 
  have eq2 : a 0 * r * (1 + r ^ 2) = 40 := by
    nlinarith
  have hr2 : r = 2 := by 
    nlinarith [sq_nonneg (r - 2), sq_nonneg (a 0 - 4)]
  have ha0 : a 0 = 4 := by
    rw [hr2] at eq1
    nlinarith 
  have h1 : ∀ (k : ℕ), ∑ i in Finset.range k, a i = 4 * ((2: ℝ) ^ k - 1) := by
    intro k 
    induction k with 
    | zero =>
      simp [Finset.sum_range_zero, hr2, ha0, hr]
      all_goals norm_num 
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp [hr2, ha0, hr]
      all_goals ring_nf 
  have h2 : 4 * ((2: ℝ) ^ n - 1) = 1020 := by
    specialize h1 n 
    nlinarith [h1, hS]
  have h3 : (2 : ℝ) ^ n = 256 := by 
    nlinarith
  have h4 : n = 8 := by
    have h5 : (2 : ℝ) ^ n = 256 := h3 
    have h6 : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num 
    rw [h6] at h5 
    have h7 : (2 : ℝ) ^ n = (2 : ℝ) ^ (8 : ℕ) := by
      exact_mod_cast h5 
    have h8 : n = 8 := by
      exact Nat.cast_injective ((by simpa using h7) : (n : ℕ) = (8 : ℕ))
    exact h8
  exact h4