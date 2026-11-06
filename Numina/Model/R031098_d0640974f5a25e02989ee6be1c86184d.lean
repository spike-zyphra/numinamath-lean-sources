import Mathlib

open Finset

theorem algebra_440955 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (hinc : ∀ n, a n < a (n + 1)) (h1 : a 0 + a 2 = 5) (h2 : a 0 + 3 + (a 2 + 4) = 2 * (3 * a 1)) :
    ∀ n, a n = 2 ^ n ∧ ∑ i ∈ range n, Real.log (a (3 * i + 3)) = 3 * n * (n + 1) / 2 * Real.log 2 := by
  rcases ha with ⟨r, hr⟩
  have h3 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr
  have h4 : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    simpa using hr
  rw [h3] at h1
  rw [h4] at h2
  have h5 : r > 1 := by
    have h6 : a 0 < a 1 := by
      specialize hinc 0
      simpa using hinc
    have h7 : a 0 > 0 := by
      by_contra h
      push_neg at h
      have : a 0 ≤ 0 := by linarith
      nlinarith [h6, hr 1, hr 0]
    nlinarith
  have h8 : a 0 > 0 := by
    by_contra h
    push_neg at h
    have : a 0 ≤ 0 := by linarith
    have h9 : a 0 < a 1 := by
      specialize hinc 0
      simpa using hinc
    nlinarith [h9, hr 1, hr 0]
  -- Now solving equations
  have h9 : a 0 + a 0 * r ^ 2 = 5 := by
    linarith
  have h10 : a 0 + a 0 * r ^ 2 + 7 = 6 * (a 0 * r) := by
    nlinarith
  -- Solving for r and a_0
  have ha1 : r = 2 := by
    nlinarith [sq_pos_of_pos h8, sq_pos_of_pos (show (0:ℝ) < r by linarith [h5]), sq_nonneg (r - 2), sq_nonneg (a 0 - 1)]
  have ha0 : a 0 = 1 := by
    rw [ha1] at h9
    nlinarith
  have h9 : ∀ n, a n = 2 ^ n := by
    intro n
    have h9 : a n = a 0 * r ^ n := by
      specialize hr n
      simpa using hr
    rw [h9]
    rw [ha0, ha1]
    all_goals norm_num
  intro n
  constructor
  · -- Show that a_n = 2^n
    specialize h9 n
    simpa using h9
  · -- Show that the sum is 3n(n+1)/2 * ln 2
    have h10 : ∀ i: ℕ, Real.log (a (3 * i + 3)) = 3 * (i + 1 : ℝ) * Real.log 2 := by
      intro i
      have ha3i3 : a (3 * i + 3) = (2 : ℝ) ^ (3 * i + 3) := by
        have h9_1 : ∀ n, a n = 2 ^ n := by
          intro n
          have h9 : a n = a 0 * r ^ n := by
            specialize hr n
            simpa using hr
          rw [h9]
          rw [ha0, ha1]
          all_goals norm_num
        specialize h9_1 (3 * i + 3)
        simpa using h9_1
      rw [ha3i3]
      have h11 : Real.log ((2 : ℝ) ^ (3 * i + 3)) = (3 * i + 3) * Real.log 2 := by
        simp [Real.log_pow]
      rw [h11]
      ring
    have h11 : ∀ n: ℕ, ∑ i ∈ range n, Real.log (a (3 * i + 3)) = 3 * n * (n + 1) / 2 * Real.log 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [sum_range_succ, ih]
        simp [h10]
        field_simp
        ring
    specialize h11 n
    linarith