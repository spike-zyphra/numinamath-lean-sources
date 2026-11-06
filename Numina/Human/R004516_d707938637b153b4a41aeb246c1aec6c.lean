import Mathlib
open Nat Real Finset Set

/-378. Find the condition under which the product of two arbitrary terms of a geometric progression will be a term of the same progression.-/
theorem algebra_200002 {a q : ℝ} (hq : q ≠ 0) :
  (∀ n m : ℤ, ∃ k : ℤ, a * q ^ n * a * q ^ m = a * q ^ k) ↔
  (a = 0 ∨ ∃ l : ℤ, a = q ^ l) := by
  -- Prove both directions: necessity and sufficiency .
  constructor
  -- Necessity: If the product condition holds for all $n$, $m$, then $a = 0$ or $a = q^l$.
  { intro h
    by_cases ha : a = 0
    { left
      exact ha }
    { right
      have h_nm : ∃ k : ℤ, a * q ^ 0 * a * q ^ 0 = a * q ^ k := h 0 0
      have h_simp : a * q ^ 0 * a * q ^ 0 = a ^ 2 := by
        rw [pow_zero, mul_one, mul_one]
        ring
      obtain ⟨k, hk⟩ := h_nm
      have h_eq : a ^ 2 = a * q ^ k := by rwa [h_simp] at hk
      have h_div : a = q ^ k := by
        rw [pow_two] at h_eq
        exact (mul_right_inj' ha).mp h_eq
      use k } }
  -- Sufficiency: $If a = 0$ or $a = q^l$, then the product condition holds for all $n$, $m$.
  { intro h
    intro n m
    cases h with
    | inl ha =>
      -- Case: $a = 0$, the product is trivially $0$.
      have h_left : a * q ^ n * a * q ^ m = 0 := by
        rw [ha, zero_mul]
        ring
      use 0
      have h_right : a * q ^ 0 = 0 := by
        rw [ha, zero_mul]
      rw [h_left, h_right.symm]
      rfl
    | inr h_exists =>
      -- Case: $a = q^l$, show the product equals $a * q^k$ for some $k$.
      obtain ⟨l, ha⟩ := h_exists
      have h_left : a * q ^ n * a * q ^ m = q ^ (2 * l + n + m) := by
        rw [ha]
        rw [← zpow_add₀ hq l n]
        rw [← zpow_add₀ hq (l + n) l]
        rw [← zpow_add₀ hq (l + n + l) m]
        ring_nf
      use l + n + m
      rw [h_left, ha, ← zpow_add₀ hq l (l + n + m)]
      apply congr_arg
      ring }
