import Mathlib
/- solve in the set of real numbers the equation $x^2 + ⌊ x ⌋ {x} + 3{x}^2 = 4$ -/
theorem algebra_112955 (x : ℝ) (hx : x^2 + 2 * ⌊x⌋ * (x - ⌊x⌋) + 3 * (x - ⌊x⌋)^2 = 4) :
    x = -5 / 2 ∨ x = -2 ∨ x = 2 ∨ x = 3 / 2 := by
  have h1 : (2 * x - ⌊x⌋) ^ 2 = 4 := by
    have h_eq : x ^ 2 + 2 * ⌊x⌋ * (x - ⌊x⌋) + 3 * (x - ⌊x⌋) ^ 2 = 4 := hx
    ring_nf at h_eq
    nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
  have h2 : 2 * x - ⌊x⌋ = 2 ∨ 2 * x - ⌊x⌋ = -2 := by
    have h_eq : (2 * x - ⌊x⌋) ^ 2 - 4 = 0 := by linarith
    have h_factored : ((2 * x - ⌊x⌋) - 2) * ((2 * x - ⌊x⌋) + 2) = 0 := by
      ring_nf at h_eq ⊢
      linarith
    cases (mul_eq_zero.mp h_factored) with
    | inl h1 =>
      left
      linarith
    | inr h2 =>
      right
      linarith
  cases h2 with
  | inl h2 =>
    -- Case 1: 2x - ⌊x⌋ = 2
    have h_floor_eq : ⌊x⌋ = 2 * x - 2 := by linarith
    have h_int : ∃ n : ℤ, (2 * x - 2 : ℝ) = n := by
      use ⌊x⌋
      rw [h_floor_eq]
    rcases h_int with ⟨n, hn⟩
    have h3 : (2 * x - 2 : ℝ) = n := hn
    have h4 : (n : ℝ) ≤ (x : ℝ) := by
      have h_floor_le : ⌊x⌋ ≤ x := Int.floor_le x
      rw [h_floor_eq] at h_floor_le
      linarith
    have h5 : (x : ℝ) < (n : ℝ) + 1 := by
      have h_floor_lt : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
      rw [h_floor_eq] at h_floor_lt
      linarith
    have h6 : (n : ℝ) ≤ 2 := by
      nlinarith [h3, h4]
    have h7 : (0 : ℝ) < (n : ℝ) := by
      nlinarith [h3, h5]
    have hn1 : n = 1 ∨ n = 2 := by
      have h10 : n ≤ 2 := by
        exact_mod_cast h6
      have h11 : 0 < n := by
        exact_mod_cast h7
      have : n = 1 ∨ n = 2 := by
        omega
      assumption
    cases hn1 with
    | inl hn1 =>
      -- n = 1
      have hx_eq : x = (3 : ℝ) / 2 := by
        have h12 : (n : ℝ) = 1 := by exact_mod_cast hn1
        linarith [h3, h12]
      right
      right
      right
      linarith
    | inr hn2 =>
      -- n = 2
      have hx_eq : x = 2 := by
        have h13 : (n : ℝ) = 2 := by exact_mod_cast hn2
        linarith [h3, h13]
      right
      right
      left
      linarith
  | inr h2 =>
    -- Case 2: 2x - ⌊x⌋ = -2
    have h_floor_eq : ⌊x⌋ = 2 * x + 2 := by linarith
    have h_int : ∃ m : ℤ, (2 * x + 2 : ℝ) = m := by
      use ⌊x⌋
      rw [h_floor_eq]
    rcases h_int with ⟨m, hm⟩
    have h6 : (m : ℝ) ≤ (x : ℝ) := by
      have h_floor_le : ⌊x⌋ ≤ x := Int.floor_le x
      rw [h_floor_eq] at h_floor_le
      linarith
    have h7 : (x : ℝ) < (m : ℝ) + 1 := by
      have h_floor_lt : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
      rw [h_floor_eq] at h_floor_lt
      linarith
    have h8 : (m : ℝ) ≤ -2 := by
      nlinarith [h6, hm]
    have h9 : (m : ℝ) > -4 := by
      nlinarith [h7, hm]
    have h10 : m ≤ -2 := by
      exact_mod_cast h8
    have h11 : -4 < m := by
      exact_mod_cast h9
    have h12 : m = -3 ∨ m = -2 := by
      omega
    cases h12 with
    | inl hm1 =>
      -- m = -3
      have hx_eq : x = -5 / 2 := by
        have h13 : (m : ℝ) = -3 := by exact_mod_cast hm1
        linarith [hm, h13]
      left
      linarith
    | inr hm2 =>
      -- m = -2
      have hx_eq : x = -2 := by
        have h14 : (m : ℝ) = -2 := by exact_mod_cast hm2
        linarith [hm, h14]
      right
      left
      assumption
