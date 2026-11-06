import Mathlib

open Real Set Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem algebra_2081 {m : ℝ} (F : ℝ → ℝ) (hF : F = λ x => (6 * x ^ 2 + 16 * x + 3 * m) / 6)
    (hF1 : ∃ a b : ℝ, ∀ x : ℝ, F x = (a*x+b) ^ 2) :
    (m ∈ Set.Ioo 3 4) := by
  rcases hF1 with ⟨a, b, h_eq⟩
  have eq4 : ∀ x : ℝ, (6 * x ^ 2 + 16 * x + 3 * m) / 6 = (a * x + b) ^ 2 := by
    intro x
    have eq := h_eq x
    simpa [hF] using eq
  have h1 : a ^ 2 = 1 := by
    have eq5 := eq4 0
    have eq6 := eq4 1
    have eq7 := eq4 2
    ring_nf at eq5 eq6 eq7
    nlinarith [sq_nonneg (a * (1 : ℝ) + b), sq_nonneg (a * (2 : ℝ) + b), sq_nonneg (a * (3 : ℝ) + b)]
  have h9 : a * b = 4 / 3 := by
    have eq6 := eq4 1
    have eq5 := eq4 0
    ring_nf at eq5 eq6
    nlinarith
  have h10 : a = 1 ∨ a = -1 := by
    have ha : a ^ 2 = 1 := h1
    have : a = 1 ∨ a = -1 := by
      rw [sq_eq_one_iff] at ha
      exact ha
    assumption
  cases h10 with
  | inl ha1 =>
    -- a = 1
    have hb1 : b = 4 / 3 := by
      rw [ha1] at h9
      nlinarith
    have hm1 : m = 32 / 9 := by
      have h50 := eq4 0
      ring_nf at h50
      rw [hb1] at h50
      nlinarith
    rw [Set.mem_Ioo] at *
    constructor
    · -- Show that 3 < m
      linarith [hm1]
    · -- Show that m < 4
      linarith [hm1]
  | inr ha2 =>
    -- a = -1
    have hb2 : b = -4 / 3 := by
      rw [ha2] at h9
      nlinarith
    have hm2 : m = 32 / 9 := by
      have h50 := eq4 0
      ring_nf at h50
      rw [hb2] at h50
      nlinarith
    rw [Set.mem_Ioo] at *
    constructor
    · -- Show that 3 < m
      linarith [hm2]
    · -- Show that m < 4
      linarith [hm2]