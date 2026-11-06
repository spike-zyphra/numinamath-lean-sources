import Mathlib

open Nat


lemma ceil_lt_add_one' {a : ℚ} (ha : -1 < a) : ⌈a⌉₊ < a + 1 := by
  by_cases w_a_nonneg : a ≥ 0
  . exact ceil_lt_add_one w_a_nonneg
  . have : ⌈a⌉₊ = 0 := by
      refine ceil_eq_zero.mpr ?_
      linarith
    rw [this]
    norm_cast
    linarith

theorem number_theory_635434 {N : ℕ} (hN : N ≥ 3) :
    IsLeast {m | 10 ^ (N - 1) ≤ m ∧ m < 10 ^ N ∧ 3 * m % 23 = 5 ∧ 4 * m % 25 = 11} (575 * ⌈((10 ^ (N - 1) - 109) / 575 : ℚ)⌉₊ + 109) := by
  have solve_congruence m : 3 * m % 23 = 5 ∧ 4 * m % 25 = 11 ↔ m % 575 = 109 := by
    -- No explicit call of the Chinese remainder theorem is needed.
    omega
  simp only [solve_congruence]
  set y : ℚ := (10 ^ (N - 1) - 109) / 575
  constructor
  . constructor
      -- We show that the choice of $y$ satisfies the lower bound constraints.
    . have : y ≤ ⌈y⌉₊ := by
        exact le_ceil y
      qify
      calc
        10 ^ (N - 1) = 575 * y + 109 := by
          unfold y
          ring
        _ ≤ 575 * ⌈y⌉₊ + 109 := by linarith
    constructor
    -- We show the choice of $y$ satisfies the upper bound contraints
    . have : 10 ^ (N - 1) ≥ 10 ^ 2 := by
        have : N - 1 ≥ 2 := by
          omega
        gcongr
        simp
      have : ⌈y⌉₊ < y + 1 := by
        refine ceil_lt_add_one' ?_
        qify at this
        unfold y
        linarith
      suffices 575 * (y + 1) + 109 < 10 ^ N by
        qify
        linarith
      unfold y
      ring_nf
      norm_cast
      suffices 575 < 9 * 10 ^ (N - 1) by
        rw [show (10 ^ N = 10 ^ (N - 1 + 1)) by congr; omega]
        ring_nf
        linarith
      linarith
    . omega
  -- We show that the choice of $y$ is the smallest such that both inequalities are satisfied.
  . simp [lowerBounds]
    intro m _10_pow_N_sub_1_le_m m_lt_10_pow_N m_mod_575_eq_109
    have div_add_mod_eq_m := Nat.div_add_mod m 575
    rw [←div_add_mod_eq_m, m_mod_575_eq_109]
    set q := m / 575
    suffices ⌈y⌉₊ ≤ q by
      linarith
    unfold y
    have : q = ⌈((m - 109) / 575 : ℚ)⌉₊ := by
      have : ((m - 109) / 575 : ℚ) = q := by
        rw [←div_add_mod_eq_m, m_mod_575_eq_109]
        simp
      simp [this]
    rw [this]
    have : ((10 ^ (N - 1) - 109) / 575 : ℚ) ≤ (m - 109) / 575 := by
      qify at _10_pow_N_sub_1_le_m
      linarith
    exact ceil_le_ceil this


