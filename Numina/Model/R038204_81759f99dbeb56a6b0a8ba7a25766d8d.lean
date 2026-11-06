import Mathlib

theorem algebra_311896 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ m n, m > 0 ∧ n > 0 ∧ m^2 - a * m + b = 0 ∧ n^2 - a * n + b = 0)
    (h2 : ∃ p q, p > 0 ∧ q > 0 ∧ p^2 - b * p + a = 0 ∧ q^2 - b * q + a = 0) :
    (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) ∨ (a = 4 ∧ b = 4) := by
  rcases h1 with ⟨m, n, hm, hn, he1, he2⟩
  rcases h2 with ⟨p, q, hp, hq, he3, he4⟩
  have h12 : m ≤ a := by
    by_contra h12
    push_neg at h12
    have h13 : m > a := h12
    have he11 : m ^ 2 < a * m := by
      omega
    nlinarith
  have h13 : n ≤ a := by
    by_contra h13
    push_neg at h13
    have h14 : n > a := h13
    have he11 : n ^ 2 < a * n := by
      omega
    nlinarith
  have h14 : p ≤ b := by
    by_contra h14
    push_neg at h14
    have h15 : p > b := h14
    have he11 : p ^ 2 < b * p := by
      omega
    nlinarith
  have h15 : q ≤ b := by
    by_contra h15
    push_neg at h15
    have h16 : q > b := h15
    have he11 : q ^ 2 < b * q := by
      omega
    nlinarith
  have h28 : a ≤ 6 := by
    nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (p - q : ℤ), he1, he2, he3, he4, mul_pos ha hb, hm, hn, hp, hq]
  have h29 : b ≤ 6 := by
    nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (p - q : ℤ), he1, he2, he3, he4, mul_pos ha hb, hm, hn, hp, hq]
  interval_cases a <;> interval_cases b <;> omega