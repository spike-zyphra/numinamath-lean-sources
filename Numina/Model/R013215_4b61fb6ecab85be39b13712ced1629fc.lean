import Mathlib

theorem number_theory_19606 (x : ℕ) (hx : x = 735) :
    IsLeast {n | ∃ a : ℕ, a > 0 ∧ n^2 = a * x} 105 := by
  rw [hx]
  constructor
  · -- First, show 105 is in the set
    use 15
    all_goals norm_num
  · -- Now, prove the minimality of 105
    intro n hn
    rcases hn with ⟨a, ha, hn⟩
    by_contra h
    push_neg at h
    have h1 : n < 105 := h
    have h2 : a * 735 = n ^ 2 := by
      linarith [hn]
    have h4 : n > 0 := by
      by_contra h
      push_neg at h
      have : n ≤ 0 := by linarith
      have : n = 0 := by linarith
      rw [this] at h2
      have h3 : a * 735 = 0 := by linarith
      have h4 : a = 0 := by
        nlinarith
      linarith
    have h5 : n ≤ 104 := by
      linarith
    have h3 : a ≤ 14 := by
      nlinarith [h2, h5, h4]
    interval_cases a <;> try { 
      interval_cases n <;> omega 
    }