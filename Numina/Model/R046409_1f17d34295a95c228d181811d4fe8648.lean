import Mathlib

theorem algebra_325388 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 - b^2 - c^2 = a * b * c) (h2 : a^2 = 2 * (b + c)) :
    a = 2 ∧ b = 1 ∧ c = 1 := by
  have ha2 : a % 2 = 0 := by 
    have h2' : a^2 % 2 = 0 := by 
      omega
    have h1 : a % 2 = 0 := by
      by_contra h
      push_neg at h
      have h3 : a % 2 = 1 := by 
        omega
      have h4 : a^2 % 2 = 1 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      omega
    exact h1
  have ha2k : ∃ k : ℤ, a = 2 * k := by
    refine' ⟨a / 2, by omega⟩
  rcases ha2k with ⟨k, hk⟩
  have eq1 : b + c = 2 * k^2 := by
    rw [hk] at h2
    have eq1 : 4 * k^2 = 2 * (b + c) := by
      nlinarith
    linarith
  have eq2 : (2 * k)^2 - b^2 - c^2 = (2 * k) * b * c := by 
    rw [hk] at h1 
    linarith
  have hk1 : k = 1 := by
    have ha_pos : 0 < k := by
      nlinarith [hk, ha]
    have hk2 : k ≤ 1 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (k * b - k * c), sq_nonneg (b + c - 2), sq_nonneg (k - 1), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have hk_pos : k ≥ 1 := by 
      omega
    have : k = 1 := by 
      nlinarith
    linarith
  -- Compute a, b, c from k = 1
  have ha2 : a = 2 := by 
    linarith [hk, hk1]
  have eq4 : b + c = 2 := by
    rw [hk1] at eq1 
    linarith
  have hb1 : b = 1 := by
    have h3 : b < 2 := by 
      nlinarith [eq4, hc]
    interval_cases b <;> omega
  have hc1 : c = 1 := by 
    linarith [eq4, hb1]
  exact ⟨ha2, hb1, hc1⟩