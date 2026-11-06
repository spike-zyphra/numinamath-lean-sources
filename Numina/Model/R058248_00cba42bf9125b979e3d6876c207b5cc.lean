import Mathlib

theorem algebra_251654 {a b r : ℤ} (ha : a ≠ b) (h : (r - a) * (r - b) = -1) : a + b = 2 * r := by
  have h1 : (r - a) = 1 ∨ (r - a) = -1 := by 
    have h1 : (r - a) ∣ -1 := ⟨r - b, by linarith⟩
    have h2 : (r - a) ∣ 1 := by 
      exact Int.dvd_neg.mp h1
    have h3 : (r - a) = 1 ∨ (r - a) = -1 := by 
      obtain ⟨k, hk⟩ := h2 
      have : (r - a) * k = 1 := by
        linarith 
      have h4 : (r - a) = 1 ∨ (r - a) = -1 := by 
        apply Int.eq_one_or_neg_one_of_mul_eq_one 
        linarith 
      exact h4 
    exact h3 
  rcases h1 with (h1 | h1)
  · -- Case 1: r - a = 1, so r = a + 1
    have hr1 : r = a + 1 := by linarith 
    have h2 : (r - b) = -1 := by 
      rw [h1] at h 
      linarith 
    have hr2 : r = b - 1 := by linarith 
    linarith [hr1, hr2] 
  · -- Case 2: r - a = -1, so r = a - 1
    have hr1 : r = a - 1 := by linarith 
    have h2 : (r - b) = 1 := by 
      rw [h1] at h 
      linarith 
    have hr2 : r = b + 1 := by linarith 
    linarith [hr1, hr2]