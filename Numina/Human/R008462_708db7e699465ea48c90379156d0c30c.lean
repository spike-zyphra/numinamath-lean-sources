import Mathlib

open Real

theorem algebra_122742 :
    IsLeast {n : ℕ | n > 0 ∧ ∑ i ∈ Finset.Icc 1 n, sin (i * π / 9) = (1 / 2) * tan (4 * π / 9)} 4 := by
  have H₁ (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, 2 * sin (π / 18) * sin (i * π / 9) = cos (π / 18) - cos ((2 * n + 1) * π / 18) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by simp), ih, Real.two_mul_sin_mul_sin]
      rw [show π / 18 - ↑(n + 1) * π / 9 = -((2 * ↑n + 1) * π / 18) by simp; ring,
          cos_neg,
          show π / 18 + ↑(n + 1) * π / 9 = (2 * ↑(n + 1) + 1) * π / 18 by simp; ring]
      ring_nf
  have h₁ : 0 < sin (π / 18) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have H₂ (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, sin (i * π / 9) = (1 / 2) * tan (4 * π / 9) ↔ ∃ k, n = 9 * k + 4 := by
    calc ∑ i ∈ Finset.Icc 1 n, sin (i * π / 9) = (1 / 2) * tan (4 * π / 9)
      _ ↔ 2 * sin (π / 18) * ∑ i ∈ Finset.Icc 1 n, sin (i * π / 9) = 2 * sin (π / 18) * ((1 / 2) * tan (4 * π / 9)) := by
        refine (mul_right_inj' ?_).symm
        simp
        exact ne_of_gt h₁
      _ ↔ cos (π / 18) - cos ((2 * n + 1) * π / 18) = cos (π / 18) := by
        rw [iff_eq_eq]
        congr
        . rw [Finset.mul_sum, H₁]
        . ring_nf
          rw [show π * (4 / 9) = π / 2 - π / 18 by ring,
              Real.tan_pi_div_two_sub,
              tan_eq_sin_div_cos]
          field_simp
      _ ↔ cos ((2 * n + 1) * π / 18) = 0 := sub_eq_self
      _ ↔ ∃ k : ℤ, (2 * n + 1) * π / 18 = (2 * k + 1) * Real.pi / 2 := Real.cos_eq_zero_iff
      _ ↔ ∃ k, n = 9 * k + 4 := by
        constructor
        . rintro ⟨k, hk⟩
          replace hk : n * π = (9 * k + 4) * π := by linarith only [hk]
          rw [mul_left_inj' pi_ne_zero] at hk
          norm_cast at hk
          have kpos : 0 ≤ k := by omega
          obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k' = k := CanLift.prf k kpos
          exact ⟨k, by norm_cast at hk⟩
        . rintro ⟨k, rfl⟩
          use k
          simp
          ring
  conv_lhs =>
    ext n
    rw [Set.setOf_app_iff, H₂]
  change IsLeast {n | n > 0 ∧ ∃ k, n = 9 * k + 4} 4
  constructor
  . simp
  . rintro n ⟨npos, ⟨k, rfl⟩⟩
    simp