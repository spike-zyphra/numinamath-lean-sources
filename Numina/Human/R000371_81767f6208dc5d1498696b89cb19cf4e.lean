import Mathlib

open Polynomial


/-
The polynomial $x^{2}-8x+k$ is a perfect square trinomial. Find the value of $k$.
-/

theorem algebr_9259 (k : ℝ) :
    IsSquare ((X : ℝ[X]) ^ 2 - 8 * X + C k) ↔ k = 16 := by

  constructor
  . intro h

    -- let $x ^ 2 - 8x + k = (a x + b) ^ 2 = a ^ 2 x ^ 2 + 2 ab x + b ^ 2$

    obtain ⟨c, hc⟩ := (isSquare_iff_exists_sq _).mp h

    have : c.natDegree = 1 := by
      have : (X ^ 2 - 8 * X + C k).natDegree = 2 := by
        have : X ^ 2 - 8 * X = C (1:ℝ) * X ^ 2 + C (-8) * X := by
          rw [show C (1:ℝ) = 1 by rfl, one_mul,
              show C (-8 : ℝ) = -8 by simp; rfl, sub_eq_add_neg, neg_mul]
        rw [this]
        apply natDegree_quadratic
        linarith
      rw [hc, natDegree_pow] at this
      linarith
    obtain ⟨a, ⟨_, ⟨b, hab⟩⟩⟩ := natDegree_eq_one.mp this

    have : c ^ 2 = C (a ^ 2) * X ^ 2 + C (2 * a * b) * X + C (b ^ 2) := by
      rw [← hab, add_pow_two,
          show (C a * X) ^ 2 = C (a ^ 2) * X ^ 2 by rw [mul_pow, ← C_pow],
          show 2 * (C a * X) * C b = C (2 * a * b) * X by rw [C_mul, C_mul, show C (2 : ℝ) = (2 : ℝ[X]) by rfl]; ring,
          C_pow, C_pow]
    rw [this] at hc

    set p1 := X ^ 2 - 8 * X + C k with hp1
    set p2 := C (a ^ 2) * X ^ 2 + C (2 * a * b) * X + C (b ^ 2) with hp2

    -- $a ^ 2 = 1$

    have r1 : a ^ 2 = 1 := by
      have t1 : (C a ^ 2 * X ^ 2).coeff 2 = a ^ 2 := by
        rw [← C_pow, coeff_C_mul]
        simp
      have t2 : (C b ^ 2).coeff 2 = 0 := by
        rw [← C_pow]
        exact coeff_C_succ
      have : p2.coeff 2 = 1 := by simp [← hc, hp1, coeff_X_of_ne_one]
      rw [← this, hp2]
      simp [t1, t2]

    -- $2ab = -8$
    have r2 : 2 * a * b = -8 := by
      have t1 : (C a ^ 2 * X ^ 2).coeff 1 = 0 := by
        rw [← C_pow, coeff_C_mul]
        simp
      have t2 : (C b ^ 2).coeff 1 = 0 := by
        rw [← C_pow]
        exact coeff_C_succ
      have : p2.coeff 1 = -8 := by simp [← hc, hp1]
      rw [← this, hp2]
      simp [t1, t2]

    -- $b ^ 2 = k$
    have r3 : b ^ 2 = k := by
      have : p2.coeff 0 = k := by simp [← hc, hp1]
      rw [← this, hp2]
      simp
      rw [← C_pow]
      exact coeff_C_zero.symm

    -- then we get $k = 16$.
    have : (2 * a * b) ^ 2 = (-8) ^ 2 := congrFun (congrArg HPow.hPow r2) 2
    rw [mul_pow, mul_pow, r1, r3] at this
    linarith

  -- verify that k = 16 is correct.
  . intro hk
    rw [hk, pow_two, show C 16 = (16 : ℝ[X]) by rfl]
    have : (X : ℝ[X]) * X - 8 * X + 16 = (X - 4) ^ 2 := by
      rw [pow_two, mul_sub, sub_mul, sub_mul, mul_comm X 4,
          ← sub_add, sub_sub, ← two_mul, ← mul_assoc]
      ring
    rw [this]
    exact IsSquare_sq (X - C 4)
