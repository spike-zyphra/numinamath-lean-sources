import Mathlib

theorem algebra_21637 (f g : ℝ → ℝ) (hf : f = fun x => x ^ 4) (hg : g = fun x => 7 * x ^ 2 - 10)
    (m n : ℝ) (hm : m > n) (hfg : f (Real.sqrt m) = g (Real.sqrt m)) (hfg' : f (-Real.sqrt m) = g (-Real.sqrt m))
    (hfg'' : f (Real.sqrt n) = g (Real.sqrt n)) (hfg''' : f (-Real.sqrt n) = g (-Real.sqrt n)) :
    m - n = 3 := by

  have h1 : (Real.sqrt m) ^ 4 = 7 * (Real.sqrt m) ^ 2 - 10 := by
    rw [hf] at hfg
    rw [hg] at hfg
    simp at hfg ⊢
    nlinarith

  have h2 : (Real.sqrt n) ^ 4 = 7 * (Real.sqrt n) ^ 2 - 10 := by
    rw [hf] at hfg''
    rw [hg] at hfg''
    simp at hfg'' ⊢
    nlinarith

  have h3 : m ≥ 0 := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt m = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals linarith
    rw [h4] at h1
    nlinarith

  have h4 : n ≥ 0 := by
    by_contra h
    push_neg at h
    have h5 : Real.sqrt n = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals linarith
    rw [h5] at h2
    nlinarith

  have h5 : m ^ 2 - 7 * m + 10 = 0 := by
    have h6 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt (by linarith)
    have h7 : (Real.sqrt m) ^ 4 = (m) ^ 2 := by
      calc
        (Real.sqrt m) ^ 4 = ((Real.sqrt m) ^ 2) ^ 2 := by ring
        _ = (m) ^ 2 := by rw [h6]
    nlinarith [h1, h7, h6]

  have h6 : n ^ 2 - 7 * n + 10 = 0 := by
    have h7 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (by linarith)
    have h8 : (Real.sqrt n) ^ 4 = (n) ^ 2 := by
      calc
        (Real.sqrt n) ^ 4 = ((Real.sqrt n) ^ 2) ^ 2 := by ring
        _ = (n) ^ 2 := by rw [h7]
    nlinarith [h2, h8, h7]

  have h7 : m = 5 ∨ m = 2 := by
    have h8 : m ^ 2 - 7 * m + 10 = 0 := h5
    have h9 : (m - 5) * (m - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- m - 5 = 0, so m = 5
      left
      linarith
    · -- m - 2 = 0, so m = 2
      right
      linarith

  have h8 : n = 5 ∨ n = 2 := by
    have h9 : n ^ 2 - 7 * n + 10 = 0 := h6
    have h10 : (n - 5) * (n - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- n - 5 = 0, so n = 5
      left
      linarith
    · -- n - 2 = 0, so n = 2
      right
      linarith

  cases h7 with
  | inl h9 =>
    cases h8 with
    | inl h10 =>
      exfalso
      linarith
    | inr h11 =>
      nlinarith
  | inr h9 =>
    cases h8 with
    | inl h10 =>
      nlinarith
    | inr h11 =>
      exfalso
      linarith