import Mathlib

open Real

/- x can be normalized to [0, π)  -/
lemma exists_zero_le_lt_pi (x:ℝ):
  ∃ (k:ℤ), k*π ≤ x ∧ x < (k+1)*π := by
  use ⌊x/π⌋
  constructor
  · have: ⌊x / π⌋ ≤ x/π := Int.floor_le (x / π)
    exact (le_div_iff₀ pi_pos).mp this
  · have: x/π < ⌊x/π⌋ + 1 := by
      exact Int.lt_floor_add_one (x / π)
    exact (mul_inv_lt_iff₀ pi_pos).mp this

/- x can be normalized to [-π/2, π/2)  -/
lemma exists_neg_pi_div_two_le_lt_pi_div_two (x:ℝ):
  ∃ (k:ℤ), - (π/2) + k*π ≤ x ∧ x < (π/2) + k*π := by
  rcases (exists_zero_le_lt_pi x) with ⟨k, hk⟩
  by_cases h: x - (k+1)*π ≥ -(π/2)
  · use (k+1)
    push_cast
    constructor
    · linarith only [h]
    · linarith only [hk.right, pi_pos]
  · push_neg at h
    replace h: x - k*π < π/2 := by
      linarith only [h]
    use k
    constructor
    · linarith only [hk.left, pi_pos]
    · linarith only [h]

/- if tan x = 1, then x = π/4 + kπ -/
lemma tan_eq_one_iff {x:ℝ}:
  tan x = 1 ↔ ∃ (k:ℤ), x = π/4 + k * π := by
  rcases (exists_neg_pi_div_two_le_lt_pi_div_two x) with
    ⟨k, hx1, hx2⟩
  replace hx1: -(π/2) ≤ x - k*π := by linarith only [hx1]
  replace hx2: x - k*π < π/2 := by linarith only [hx2]
  have: x = (x - k*π) + k*π := by simp
  constructor
  · rw [this, tan_add_int_mul_pi, ← tan_pi_div_four]
    intro h
    use k
    simp only [add_left_inj]
    by_cases hh: -(π/2) = x - k*π
    · rw [← hh, tan_neg, tan_pi_div_two,
      tan_pi_div_four] at h
      norm_num at h
    · replace hx1 := lt_of_le_of_ne hx1 hh
      apply tan_inj_of_lt_of_lt_pi_div_two hx1 hx2 ?_ ?_ h
      <;> linarith only [pi_pos]
  · rintro ⟨k,hk⟩
    rw [hk, tan_add_int_mul_pi, tan_pi_div_four]

/- 11. The solution set of the equation $[\tan x]=2 \cos ^{2} x$ is $\qquad$ -/
theorem number_theory_8301 {x:ℝ} (h: cos x ≠ 0):
  ⌊tan x⌋ = 2 * (cos x)^2 ↔ ∃ (k:ℤ), x = π/4 + k * π := by

  rw [← tan_eq_one_iff]
  constructor

  · intro heq
    -- notice that (cos x)^2 = 1 / (1 + (tan x)^2)
    rw [← inv_one_add_tan_sq h] at heq
    -- consider value of tan x. we can see floor tan x > 0.
    have h1: 0 < ⌊tan x⌋ := by
      rify
      rw [heq]
      apply mul_pos (by norm_num) ?_
      rw [inv_pos]
      linarith only [sq_nonneg (tan x)]
    have h1': ⌊tan x⌋ ≥ 1 := by exact h1
    rw [Int.floor_pos] at h1
    -- but if tan x ≥ 1, floor tan x ≤ 1 from the given equation
    have h2: ⌊tan x⌋ ≤ 1 := by
      rify
      rw [heq]
      have: 1 + (tan x)^2 ≥ 2 := by
        have: (tan x)^2 ≥ 1 := one_le_pow₀ h1
        linarith only [this]
      refine mul_inv_le_one_of_le₀ this ?_
      linarith only [this]
    -- then tan x = 1
    have h3: 2 * (1 + (tan x)^2)⁻¹ = 1 := by
      rw [← heq]
      norm_cast
      apply le_antisymm h2 h1'
    replace h3: (tan x)^2 = 1 := by
      field_simp at h3
      linarith only [h3]
    replace h3: tan x = 1 := by
      rw [sq_eq_one_iff] at h3
      rcases h3 with h3 | h3
      <;> linarith only [h3, h1]
    exact h3

  · intro hh
    rw [← inv_one_add_tan_sq h]
    norm_num [hh]