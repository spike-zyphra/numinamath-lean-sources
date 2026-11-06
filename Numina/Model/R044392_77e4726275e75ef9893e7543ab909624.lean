import Mathlib

theorem algebra_317747 {a b c : ℝ} (ha : a < b) (h : ∀ x, a * x ^ 2 + b * x + c ≥ 0) :
    (b - a) / (a + b + c) ≤ 1 / 3 := by
  have h1 := h 1
  have h2 := h (-2)
  have h3 := h (-1)
  have h4 := h 0
  have h5 := h 2
  by_cases h9 : a + b + c > 0
  · -- Case 1: if $a + b + c > 0$
    have h10 : 3 * (b - a) ≤ a + b + c := by
      nlinarith
    have h11 : (b - a) / (a + b + c) ≤ 1 / 3 := by
      have h12 : a + b + c > 0 := h9
      apply (div_le_div_iff (by linarith) (by linarith)).mpr
      linarith
    linarith
  · -- Case 2: if $a + b + c \leq 0$
    have h10 : a + b + c ≤ 0 := by linarith
    have h11 : a + b + c ≥ 0 := by
      specialize h 1
      linarith
    have h12 : a + b + c = 0 := by linarith
    rw [h12]
    norm_num
    all_goals nlinarith