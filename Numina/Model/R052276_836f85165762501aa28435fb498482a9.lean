import Mathlib

theorem algebra_13024 (x : ℝ) :
    2 * ⌊x⌋ ^ 2 + 2 * x - 1 = 0 ↔ x = 0.5 ∨ x = -0.5 := by
  constructor
  · -- Forward: Assume $2 * ⌊x⌋^2 + 2 * x - 1 = 0$, prove $x = 0.5 ∨ x = -0.5$
    intro h
    let n := ⌊x⌋
    have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : 2 * (n : ℝ) ^ 2 + 2 * x - 1 = 0 := by linarith
    have h4 : x = (1 - 2 * (n : ℝ) ^ 2) / 2 := by linarith
    rw [h4] at h1
    have h5 : n ≤ 0 := by
      by_contra h'
      push_neg at h'
      have h6 : n ≥ 1 := by omega
      have h7 : (n : ℝ) ≥ 1 := by exact_mod_cast h6
      nlinarith [sq_nonneg ((n : ℝ) : ℝ), sq_nonneg (x), sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (n + 1 : ℝ))]
    have h6 : n ≥ -1 := by
      by_contra h'
      push_neg at h'
      have h7 : n ≤ -2 := by omega
      have h8 : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h7
      nlinarith [sq_nonneg ((n : ℝ) : ℝ), sq_nonneg (x), sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (n + 1 : ℝ))]
    have h9 : n = 0 ∨ n = -1 := by omega
    rcases h9 with h_n | h_n
    · -- Case n = 0
      have h10 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast h_n
      rw [h10] at h4
      have hx : x = (0.5 : ℝ) := by linarith
      left
      exact_mod_cast hx
    · -- Case n = -1
      have h11 : (n : ℝ) = (-1 : ℝ) := by exact_mod_cast h_n
      rw [h11] at h4
      have hx : x = (-0.5 : ℝ) := by linarith
      right
      exact_mod_cast hx
  · -- Backward: Assume $x = 0.5 ∨ x = -0.5$, prove $2 * ⌊x⌋^2 + 2 * x - 1 = 0$
    rintro (h | h)
    · -- Case x = 0.5
      rw [h]
      norm_num
      <;> try { native_decide }
    · -- Case x = -0.5
      rw [h]
      norm_num
      <;> try { native_decide }