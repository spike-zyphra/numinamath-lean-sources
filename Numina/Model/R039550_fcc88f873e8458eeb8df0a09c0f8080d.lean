import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185414 (k : ℝ) :
  (∀ x : ℝ, ∃ y : ℝ, y^2 = k * x^2 + k * x + 3) ↔ 0 ≤ k ∧ k ≤ 12 := by
  constructor
  · -- First direction: (∀ x : ℝ, ∃ y : ℝ, y^2 = k * x^2 + k * x + 3) implies 0 ≤ k ∧ k ≤ 12
    intro h
    have h1 := h (-1 / 2)
    rcases h1 with ⟨y1, hy1⟩
    -- At x = -1/2, compute the expression
    -- k * (-1/2)^2 + k * (-1/2) + 3 = k*(1/4) - k*(1/2) + 3 = -k/4 + 3
    -- So y₁² = 3 - k/4, since y₁² ≥ 0, then 3 - k/4 ≥ 0, hence k ≤ 12
    have h2 : 3 - k / 4 ≥ 0 := by
      nlinarith [sq_nonneg y1, hy1]
    have hk1 : k ≤ 12 := by
      linarith
    -- We need to find an `x` such that `k * x² + k * x + 3` will contradict with k < 0, let's pick x=-3/k.
    have h3 : 0 ≤ k := by 
      by_contra h4
      push_neg at h4
      -- Now `k < 0`
      have h4' : k < (0 : ℝ) := by linarith
      -- Let's pick x = -3/k which makes `k * x² + k * x + 3` negative, which contradicts $\y^2 = \text{negative value}$.
      have h5 := h (-3 / k)
      rcases h5 with ⟨y5, hy5⟩
      have hkne : k ≠ 0 := by linarith
      -- Expanding k * (-3/k)^2 + k * (-3/k) + 3
      -- k * (9/k²) - k * (3/k) + 3 = 9/k - 3 + 3 = 9/k.
      have h_eq : k * (-3 / k) ^ 2 + k * (-3 / k) + 3 = 9 / k := by
        field_simp [hkne]
        <;> ring 
      have hy5' : y5 ^ 2 = 9 / k := by 
        rw [h_eq] at hy5
        linarith  
      -- Now for the contradiction
      have h8 : 9 / k < 0 := by
        apply div_neg_of_pos_of_neg
        · norm_num
        · linarith
      have h11 : y5 ^ 2 ≥ 0 := sq_nonneg y5
      have h9 : 9 / k ≥ 0 := by linarith [hy5']
      linarith
    constructor
    · linarith
    · linarith
  · -- Second direction: (0 ≤ k ∧ k ≤ 12) implies (∀ x : ℝ, ∃ y : ℝ, y^2 = k * x^2 + k * x + 3)
    rintro ⟨hk1, hk2⟩
    intro x
    -- k * x^2 + k * x + 3 = k*(x + 1/2)^2 + (3 - k/4) ≥ 0
    -- We need this to be obviously non-negative
    have h_a_pos : 0 ≤ k * x ^ 2 + k * x + 3 := by
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg ((k ) - 12), sq_nonneg (k * (x + 1 / 2 ) ), sq_nonneg ((x + 1/2 ) * k ) ]
    use Real.sqrt (k * x ^ 2 + k * x + 3 )
    rw [Real.sq_sqrt]
    linarith