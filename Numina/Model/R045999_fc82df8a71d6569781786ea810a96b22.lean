import Mathlib

theorem inequalities_37450 (p r : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1)
    (a b c α β γ : ℝ) (h1 : ∀ x y : ℝ, (p * x + (1 - p) * y) ^ 2 = a * x ^ 2 + b * x * y + c * y ^ 2)
    (h2 : ∀ x y : ℝ, (p * x + (1 - p) * y) * (r * x + (1 - r) * y) =
      α * x ^ 2 + β * x * y + γ * y ^ 2) :
    max (max a b) c ≥ 4 / 9 ∧ max (max α β) γ ≥ 4 / 9 := by
  have hp2 : a = p ^ 2 := by
    have eq1 := h1 1 0
    have eq2 := h1 0 1
    have eq3 := h1 1 1
    ring_nf at eq1 eq2 eq3
    nlinarith
  have h1' : b = 2 * p * (1 - p) := by
    have eq1 := h1 1 1
    have eq2 := h1 1 0
    have eq3 := h1 0 1
    ring_nf at eq1 eq2 eq3
    nlinarith
  have h1'' : c = (1 - p) ^ 2 := by
    have eq1 := h1 0 1
    ring_nf at eq1
    nlinarith
  have h2' : α = p * r := by
    have eq1 := h2 1 0
    ring_nf at eq1
    nlinarith
  have h2'' : β = p + r - 2 * p * r := by
    have eq1 := h2 1 1
    have eq2 := h2 1 0
    have eq3 := h2 0 1
    ring_nf at eq1 eq2 eq3
    nlinarith
  have h2''' : γ = (1 - p) * (1 - r) := by
    have eq1 := h2 0 1
    ring_nf at eq1
    nlinarith
  constructor
  · -- Prove max (max a b) c ≥ 4 / 9
    rw [show a = p ^ 2 by linarith [hp2], show b = 2 * p * (1 - p) by linarith [h1'], show c = (1 - p) ^ 2 by linarith [h1'']]
    by_contra h
    push_neg at h
    -- Assume all coefficients a, b, c < 4/9, derive contradiction
    have h1 : p ^ 2 < 4 / 9 := by
      have h17 : max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) < 4 / 9 := by
        simpa using h
      have h18 : p ^ 2 ≤ max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) := by
        simp [max_le_iff]
      nlinarith
    have h2 : (1 - p) ^ 2 < 4 / 9 := by
      have h17 : max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) < 4 / 9 := by
        simpa using h
      have h18 : (1 - p) ^ 2 ≤ max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) := by
        simp [max_le_iff]
      nlinarith
    have h3 : p < 2 / 3 := by
      nlinarith [sq_nonneg (p - 2 / 3), h1]
    have h4 : p > 1 / 3 := by
      nlinarith [sq_nonneg (p - 1 / 3), h2]
    have h5 : 2 * p * (1 - p) ≥ 4 / 9 := by
      nlinarith [sq_nonneg (p - 1 / 2)]
    have h2p : 2 * p * (1 - p) < 4 / 9 := by
      have h17 : max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) < 4 / 9 := by
        simpa using h
      have h18 : 2 * p * (1 - p) ≤ max (max (p ^ 2 : ℝ) (2 * p * (1 - p) : ℝ)) ((1 - p) ^ 2 : ℝ) := by
        simp [max_le_iff]
      nlinarith
    linarith
  · -- Prove max (max α β) γ ≥ 4 / 9
    rw [show α = p * r by linarith [h2'], show β = p + r - 2 * p * r by linarith [h2''], show γ = (1 - p) * (1 - r) by linarith [h2''']]
    by_contra h
    push_neg at h
    -- Assume all coefficients α, β, γ < 4/9, derive contradiction
    have h1 : p * r < 4 / 9 := by
      have h21 : max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) < 4 / 9 := by
        simpa using h
      have h22 : p * r ≤ max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) := by
        simp [max_le_iff]
      nlinarith
    have h2 : p + r - 2 * p * r < 4 / 9 := by
      have h21 : max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) < 4 / 9 := by
        simpa using h
      have h212 : p + r - 2 * p * r ≤ max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) := by
        simp [max_le_iff]
      nlinarith
    have h2r : (1 - p) * (1 - r) < 4 / 9 := by
      have h221 : max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) < 4 / 9 := by
        simpa using h
      have h222 : (1 - p) * (1 - r) ≤ max (max (p * r : ℝ) (p + r - 2 * p * r : ℝ)) ((1 - p) * (1 - r) : ℝ) := by
        simp [max_le_iff]
      nlinarith
    nlinarith [sq_nonneg (p - r), sq_nonneg (p - 2 / 3), sq_nonneg (r - 2 / 3), mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2), mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2), mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hr.1), mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hr.2)]