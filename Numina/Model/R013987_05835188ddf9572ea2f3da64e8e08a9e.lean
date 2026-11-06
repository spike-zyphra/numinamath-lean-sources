import Mathlib

theorem algebra_188222 (x : ℕ → ℝ) (hx1 : x 1 = 3)
    (hxn : ∀ n ≥ 1, x (n + 1) = (x n ^ 2 + 4) / (2 * x n)) :
    ∀ n ∈ Finset.Icc 1 1000, x n > 2 := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : ∀ (n : ℕ), x (n + 1) > 2 := by
    intro n
    induction n with
    | zero =>
      rw [hx1]
      norm_num
    | succ n ih =>
      have h2 : x (n + 2) = (x (n + 1) ^ 2 + 4) / (2 * x (n + 1)) := by
        specialize hxn (n + 1) (by linarith)
        simpa using hxn
      have h3 : x (n + 1) > 0 := by
        nlinarith [ih]
      rw [h2]
      have h6 : x (n + 1) > 0 := h3
      have h7 : (x (n + 1) ^ 2 + 4) / (2 * x (n + 1)) > 2 := by
        have h8 : x (n + 1) > 0 := h6
        have h9 : x (n + 1) ^ 2 + 4 > 4 * x (n + 1) := by
          nlinarith [sq_pos_of_pos h8, sq_nonneg (x (n + 1) - 2), sq_nonneg (x (n + 1) - 2), ih]
        have h10 : (x (n + 1) ^ 2 + 4) / (2 * x (n + 1)) > 2 := by
          have h11 : 2 * x (n + 1) > 0 := by linarith
          apply (lt_div_iff' (by linarith)).mpr
          linarith
        linarith
      linarith
  have hn' : n ≥ 1 := by
    omega
  have hn_n : x n > 2 := by
    have eq2 : n ≥ 1 := by
      omega
    specialize h1 (n - 1)
    have h15 : x ((n - 1) + 1) > 2 := h1
    have eq4 : (n - 1 : ℕ) + 1 = n := by
      omega
    rw [eq4] at h15
    linarith
  simpa using hn_n