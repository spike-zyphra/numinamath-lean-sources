import Mathlib

open Real Set
open scoped Real

theorem algebra_169598 {x : ℝ} (hx : tan x * tan (x + 1) = 1) :
    ∃ k : ℤ, x = π / 4 - 1 / 2 + k * π / 2 := by

  have htan : tan x * tan (x + 1) = 1 := hx

  by_cases h1 : cos x = 0
  · -- cos x = 0, then x = π/2 + kπ
    have htan_eq_zero : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h1]
    rw [htan_eq_zero] at htan
    nlinarith

  · -- cos x ≠ 0, so tan x is defined.
    by_cases h2 : cos (x + 1) = 0
    · -- cos (x + 1) = 0, then tan (x+1) is ±infty.
      have htan1_eq_zero : tan (x + 1) = 0 := by
        rw [tan_eq_sin_div_cos]
        simp [h2]
      rw [htan1_eq_zero] at htan
      nlinarith

    · -- both cos x and cos (x + 1) ≠ 0.
      have h_eq : sin x * sin (x + 1) = cos x * cos (x + 1) := by
        have htanx : tan x = sin x / cos x := by
          rw [tan_eq_sin_div_cos]
        have htan1 : tan (x + 1) = sin (x + 1) / cos (x + 1) := by
          rw [tan_eq_sin_div_cos]
        rw [htanx, htan1] at htan
        have eq1 : (sin x / cos x) * (sin (x + 1) / cos (x + 1)) = (sin x * sin (x + 1)) / (cos x * cos (x + 1)) := by
          field_simp [show cos x ≠ 0 by assumption, show cos (x + 1) ≠ 0 by assumption]
          <;> ring
        rw [eq1] at htan
        have htan3 : sin x * sin (x + 1) / (cos x * cos (x + 1)) = 1 := htan
        field_simp [show cos x ≠ 0 by assumption, show cos (x + 1) ≠ 0 by assumption] at htan3 ⊢
        linarith

      have h_eq1 : cos (2 * x + 1) = 0 := by
        have h_eq2 : sin x * sin (x + 1) = cos x * cos (x + 1) := h_eq
        have h_eq3 : cos (2 * x + 1) = cos (x + (x + 1)) := by
          ring_nf
        have h_eq4 : cos (x + (x + 1)) = cos x * cos (x + 1) - sin x * sin (x + 1) := by
          rw [cos_add]
        have h_eq5 : cos x * cos (x + 1) - sin x * sin (x + 1) = 0 := by
          linarith [h_eq]
        rw [h_eq3, h_eq4, h_eq5]

      have h_eq2 : ∃ k : ℤ, 2 * x + 1 = Real.pi / 2 + k * Real.pi := by
        have hcos0 : cos (2 * x + 1) = 0 := h_eq1
        obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos0
        use k
        try simp at hk ⊢
        try linarith

      rcases h_eq2 with ⟨k, hk⟩
      use k
      have hk1 : (2 * x + 1) = Real.pi / 2 + k * Real.pi := hk
      have eq3 : x = (Real.pi / 2 + k * Real.pi - 1) / 2 := by
        linarith
      rw [eq3]
      field_simp
      <;> ring_nf <;> nlinarith