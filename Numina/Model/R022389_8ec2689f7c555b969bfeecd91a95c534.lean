import Mathlib

theorem algebra_210803 (m n k : ℝ) :
    (∃ x : ℝ, m * x ^ 2 + n = 0) ∧ (∃ x : ℝ, n * x ^ 2 + k = 0) ∧
    (∃ x : ℝ, k * x ^ 2 + m = 0) ↔ m = 0 ∧ n = 0 ∧ k = 0 := by
  constructor
  · -- Assume the existence of solutions, prove $m =0$, $n =0$, $k =0$
    rintro ⟨⟨x₀, h₁⟩, ⟨x₁, h₂⟩, ⟨x₂, h₃⟩⟩
    have eq1 : m * x₀ ^ 2 + n = 0 := h₁
    have eq2 : n * x₁ ^ 2 + k = 0 := h₂
    have eq3 : k * x₂ ^ 2 + m = 0 := h₃
    have h4 : n = -m * x₀ ^ 2 := by linarith
    have h5 : k = -n * x₁ ^ 2 := by linarith
    have h6 : m = -k * x₂ ^ 2 := by linarith
    rw [h4] at h5
    have eq4 : k = m * x₀ ^ 2 * x₁ ^ 2 := by
      linarith
    rw [eq4] at h6
    have eq5 : m = - (m * x₀ ^ 2 * x₁ ^ 2) * x₂ ^ 2 := by
      linarith
    have h7 : m * (1 + x₀ ^ 2 * x₁ ^ 2 * x₂ ^ 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Let h8 : m = 0
      have h_m : m = 0 := h8
      have h_n : n = 0 := by
        rw [h_m] at eq1
        linarith
      have h_k : k = 0 := by
        rw [h_n] at eq2
        linarith
      exact ⟨h_m, h_n, h_k⟩
    · -- Let h9 : 1 + x₀ ^ 2 * x₁ ^ 2 * x₂ ^ 2 = 0
      -- This is a contradiction because x₀²≥0, x₁²≥0, x₂²≥0
      have h_nonneg : x₀ ^ 2 * x₁ ^ 2 * x₂ ^ 2 ≥ 0 := by
        positivity
      nlinarith
  · -- Assume m =0 ∧ n =0 ∧ k =0, prove existence of solutions
    rintro ⟨hm, hn, hk⟩
    constructor
    · -- Finding x₀ such that 0 * x₀ ^ 2 +0 = 0
      use 0
      simp [hm, hn]
    constructor
    · -- Finding x₁ such that 0 * x₁ ^ 2 +0 = 0
      use 0
      simp [hn, hk]
    · -- Finding x₂ such that 0 * x₂ ^ 2 +0 = 0
      use 0
      simp [hk, hm]