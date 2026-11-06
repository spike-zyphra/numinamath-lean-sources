import Mathlib

theorem algebra_16506 {a b c : ℝ} (h : b ≠ c) (graph : Set (ℝ × ℝ)) (hgraph : graph = {(x, y) | x = 2 * y ^ 2 - 6 * y + 3}) (hintercept1 : (a, 0) ∈ graph) (hintercept2 : (0, b) ∈ graph) (hintercept3 : (0, c) ∈ graph) : a + b + c = 6 := by
  have ha : a = 3 := by
    rw [hgraph] at hintercept1
    simp at hintercept1
    linarith
  have hb : (0 : ℝ) = 2 * b ^ 2 - 6 * b + 3 := by 
    rw [hgraph] at hintercept2
    simp at hintercept2 
    linarith
  have hc : (0 : ℝ) = 2 * c ^ 2 - 6 * c + 3 := by
    rw [hgraph] at hintercept3 
    simp at hintercept3 
    linarith
  have heq1 : 2 * b ^ 2 - 6 * b + 3 = 0 := by
    linarith [hb]
  have heq2 : 2 * c ^ 2 - 6 * c + 3 = 0 := by 
    linarith [hc]
  have heq3 : b + c = 3 := by 
    have h1 : 2 * b ^ 2 - 6 * b + 3 = 0 := heq1 
    have h2 : 2 * c ^ 2 - 6 * c + 3 = 0 := heq2 
    have h3 : 2 * b ^ 2 - 2 * c ^ 2 - 6 * b + 6 * c = 0 := by 
      linarith [h1, h2]
    have h4 : (b - c) * (2 * (b + c) - 6) = 0 := by 
      ring_nf at h3 ⊢ 
      linarith 
    cases' (mul_eq_zero.1 h4) with h5 h6 
    · -- Assume b - c = 0, so b = c 
      exfalso 
      apply h 
      linarith 
    · -- Assume 2 * (b + c) - 6 = 0 
      linarith 
  linarith [ha, heq3]