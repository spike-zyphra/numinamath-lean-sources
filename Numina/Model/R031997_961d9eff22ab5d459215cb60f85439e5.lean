import Mathlib

theorem algebra_50475 (a : ℕ → ℝ) (h : ∃ d, ∀ n, a n = a 1 + d * (n - 1)) (ha : a 1 > 0)
    (h1 : 5 * a 13 = 6 * a 19) :
    IsLeast {n | a n < 0} 50 := by
  rcases h with ⟨d, had⟩
  have h13 : a 13 = a 1 + d * (13 - 1) := had 13
  have h19 : a 19 = a 1 + d * (19 - 1) := had 19
  rw [h13] at h1
  rw [h19] at h1
  have h2 : a 1 = -48 * d := by
    ring_nf at h1
    linarith
  have h3 : d < 0 := by
    nlinarith [ha, h2]
  
  have h4 : a 50 < 0 := by 
    have h50 : a 50 = d := by 
      rw [had 50]
      rw [h2]
      norm_num
      <;> ring
    have h53 : d < 0 := h3
    linarith [h50, h53]
  
  constructor
  · -- Show 50 is in the set
    exact h4
  · -- Show 50 is the least element in the set
    intro n hn
    have h5 : ∀ n : ℕ, a n < 0 → n ≥ 50 := by
      intro n hn
      have h6 : a n < 0 := by
        simpa using hn
      have h7 : a n = d * ((↑n : ℝ) - 49) := by
        rw [had n]
        rw [h2]
        ring_nf
      rw [h7] at h6
      by_contra h
      push_neg at h
      have h7 : n ≤ 49 := by
        omega
      have h8 : (n : ℝ) ≤ (49 : ℝ) := by
        exact_mod_cast h7
      have h9 : (n : ℝ) - 49 ≤ 0 := by
        linarith
      have h10 : d * ((n : ℝ) - 49) ≥ 0 := by
        nlinarith
      linarith
    have h6 : a n < 0 := by
      simpa using hn
    have h7 : n ≥ 50 := h5 n h6
    all_goals
      omega