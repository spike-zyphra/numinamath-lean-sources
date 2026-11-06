import Mathlib

open Real Set

theorem inequalities_37422 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    min (min u (100 / v)) (v + 2023 / u) ≤ sqrt 2123 := by
  by_contra h
  push_neg at h
  have h1 : sqrt 2123 < min (min u (100 / v)) (v + 2023 / u) := by linarith
  have h3 : sqrt 2123 < u := by
    have h3' : (min (min u (100 / v)) (v + 2023 / u)) ≤ u := by
      have h4 : (min (min u (100 / v)) (v + 2023 / u)) ≤ (min u (100 / v)) := by
        cases min_cases (min u (100 / v)) (v + 2023 / u) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      have h5 : (min u (100 / v)) ≤ u := by
        cases min_cases u (100 / v) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      linarith
    nlinarith
  have h4 : sqrt 2123 < 100 / v := by
    have h3' : (min (min u (100 / v)) (v + 2023 / u)) ≤ (100 / v) := by
      have h4 : (min (min u (100 / v)) (v + 2023 / u)) ≤ (min u (100 / v)) := by
        cases min_cases (min u (100 / v)) (v + 2023 / u) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      have h5 : (min u (100 / v)) ≤ (100 / v) := by
        cases min_cases u (100 / v) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      linarith
    nlinarith
  have h5 : sqrt 2123 < v + 2023 / u := by
    have h3' : (min (min u (100 / v)) (v + 2023 / u)) ≤ (v + 2023 / u) := by
      cases min_cases (min u (100 / v)) (v + 2023 / u) with
      | inl h =>
        linarith
      | inr h =>
        linarith
    nlinarith
  have h6 : 0 < sqrt 2123 := by
    positivity
  have h7 : sqrt 2123 ^ 2 = (2123 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have h8 : v < (100 / sqrt 2123 : ℝ) := by
    have h9 : 100 / v > sqrt 2123 := by
      linarith
    have h10 : 0 < v := hv
    have h11 : 100 > sqrt 2123 * v := by
      have h12 : 100 / v > sqrt 2123 := by linarith
      apply (lt_div_iff₀ (by linarith)).mp at h12
      nlinarith
    have h14 : sqrt 2123 > 0 := by positivity
    have h15 : v < (100 / sqrt 2123 : ℝ) := by
      have h11' : sqrt 2123 * v < (100 : ℝ) := by linarith
      have h14' : sqrt 2123 > 0 := by positivity
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h3b : 2023 / u < (2023 / sqrt 2123 : ℝ) := by
    have h10 : u > sqrt 2123 := by
      linarith
    have h11 : 0 < sqrt 2123 := by positivity
    have h12 : sqrt 2123 < u := by
      linarith
    have h13 : 0 < u := by linarith
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  have h3c : v + 2023 / u < (sqrt 2123 : ℝ) := by
    have h14 : v < (100 / sqrt 2123 : ℝ) := h8
    have h15 : 2023 / u < (2023 / sqrt 2123 : ℝ) := h3b
    have h32 : v + 2023 / u < (100 / sqrt 2123 + 2023 / sqrt 2123 : ℝ) := by
      linarith
    have h16 : (100 / sqrt 2123 + 2023 / sqrt 2123 : ℝ) = sqrt 2123 := by
      have h17 : sqrt 2123 > 0 := by positivity
      field_simp [show sqrt 2123 ≠ 0 by positivity]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2123 by norm_num : (0 : ℝ) ≤ 2123)]
    linarith [h16, h32]
  linarith