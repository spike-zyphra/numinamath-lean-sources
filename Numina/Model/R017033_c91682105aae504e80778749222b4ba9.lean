import Mathlib

theorem algebra_14418 (a b c : ℚ) (ha : a > 0) (h : a + b + c = round (a + b + c))
    (h1 : ∀ x, a * x ^ 2 + b * x + c = a * (x - 1 / 4) ^ 2 - 9 / 8) :
    a ≥ 2 / 9 := by
  have h2 := h1 0
  have h3 := h1 1
  have h4 := h1 (1 / 2)
  have h5 := h1 (-1 / 2)
  have h6 := h1 2
  norm_num at h2 h3 h4 h5 h6

  have h_a_add : a + b + c = 9 * a / 16 - 9 / 8 := by
    linarith
  have h_eq : 9 * a / 16 - 9 / 8 = round (a + b + c) := by
    linarith

  have : ∃ n : ℤ, 9 * a / 16 - 9 / 8 = n := by
    refine ⟨round (a + b + c), by rw [h_eq]⟩
  rcases this with ⟨n, hn⟩

  have eq : 9 * a = 16 * (n : ℚ) + 18 := by
    linarith
  have h_n : n ≥ -1 := by
    by_contra h_n1
    push_neg at h_n1
    have h_n2 : n ≤ -2 := by omega
    have hn16 : (n : ℚ) ≤ -2 := by exact_mod_cast h_n2
    have h_a : a ≤ 0 := by 
      nlinarith
    linarith
  have hn16 : (n : ℚ) ≥ -1 := by
    have hn16 : n ≥ -1 := h_n
    exact_mod_cast hn16
  nlinarith