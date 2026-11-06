import Mathlib

theorem algebra_76009 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≤ 100) (h2 : b ≤ 100) (h3 : c ≤ 100) :
    IsGreatest {x | ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≤ 100 ∧ b ≤ 100 ∧ c ≤ 100 ∧ a * x ^ 2 + b * x + c = 0} (-1 / 99) := by
  constructor
  · -- Show that -1/99 is in the set.
    use 99, 100, 1
    norm_num
  · -- Show that -1/99 is greatest.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1a, h2a, h3a, heq⟩
    by_contra h'
    push_neg at h'
    have h6 : x ≥ 0 := by
      omega
    have h7 : a * x ^ 2 + b * x + c > 0 := by
      have ha' : a ≥ 1 := by linarith
      have hb' : b ≥ 1 := by linarith
      have hc' : c ≥ 1 := by linarith
      have h8 : x ≥ 0 := h6
      nlinarith [sq_nonneg (x), sq_nonneg (a * x), sq_nonneg (b * x), sq_nonneg (c * x), mul_nonneg (show (0 : ℤ) ≤ x by linarith) (show (0 : ℤ) ≤ x by linarith)]
    have h8 : a * x ^ 2 + b * x + c = 0 := heq
    nlinarith