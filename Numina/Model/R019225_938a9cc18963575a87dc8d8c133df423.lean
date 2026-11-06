import Mathlib

theorem algebra_9505 {m : ℕ} (hm : m > 0) (h : ∃ x1 x2 : ℕ, x1 > 0 ∧ x2 > 0 ∧ (m^2 - 1) * x1^2 - 3 * (3 * m - 1) * x1 + 18 = 0 ∧ (m^2 - 1) * x2^2 - 3 * (3 * m - 1) * x2 + 18 = 0)
    (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : c = 2 * Real.sqrt 3)
    (h2 : m^2 + a^2 * m - 8 * a = 0) (h3 : m^2 + b^2 * m - 8 * b = 0) :
    m = 2 := by
  rcases h with ⟨x1, x2, hx1, hx2, h11, h12⟩
  have h4 : m ≤ 6 := by
    by_contra h4
    push_neg at h4
    have h5 : m ≥ 7 := by
      omega
    -- Let's prove that m > 6 is impossible
    have h6 : (m : ℕ) ≥ 7 := h5
    have h7 : m^2 ≥ 49 := by
      nlinarith [h6]
    have h9 : (m^2 : ℕ) - 1 ≥ 48 := by
      omega
    have h12 : (m^2 - 1 : ℕ) * x1^2 - 3 * (3 * m - 1) * x1 + 18 = 0 := by
      omega
    have h11 : (m^2 - 1 : ℕ) * x1^2 ≥ 48 * x1^2 := by
      have h13 : (m^2 - 1 : ℕ) ≥ 48 := by
        omega
      have h14 : (m^2 - 1 : ℕ) * x1^2 ≥ 48 * x1^2 := by
        apply Nat.mul_le_mul_right
        omega
      exact h14
    have h13 : 3 * (3 * m - 1) * x1 ≥ 60 * x1 := by
      have h14 : 3 * m - 1 ≥ 20 := by
        omega
      have h15 : 3 * (3 * m - 1) ≥ 60 := by
        omega
      have h16 : 3 * (3 * m - 1) * x1 ≥ 60 * x1 := by
        apply Nat.mul_le_mul_right
        omega
      exact h16
    have h21 : x1 ≥ 1 := by
      omega
    omega
  interval_cases m <;> try { 
    omega 
  }
  <;> try { 
    omega 
  }