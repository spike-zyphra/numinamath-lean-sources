import Mathlib

open Nat

theorem number_theory_208096 (n x y z : ℕ) (hn : n ≠ 0) :
    n ^ x + n ^ y = n ^ z ↔ n = 2 ∧ (∃ (k : ℕ), x = k ∧ y = k ∧ z = k + 1) := by 
  constructor
  -- forward direction
  · 
    intro h
  -- first prove that n ≥ 2 
    by_cases hn1 : n = 1 
    rw [hn1] at h
    simp at h
    have hn2 : n ≥ 2 := by omega
    have xley : x ≤ z := by 
      by_contra hc
      simp at hc
      have nxgt : n ^ x > n ^ z := by 
        exact (Nat.pow_lt_pow_iff_right hn2).mpr hc
      have ngtnxy : n ^ y ≥ 0 := by 
        positivity
      linarith
    have ylez : y ≤ z := by 
      by_contra hc
      simp at hc
      have nxgt : n ^ y > n ^ z := by 
        exact (Nat.pow_lt_pow_iff_right hn2).mpr hc
      have ngtnxy : n ^ x ≥ 0 := by 
        positivity
      linarith
    by_cases hy : y > x
    have eq1 : n ^ (z - x) - n ^ (y - x) = 1 := by 
      have aux : n ^ (z - x) * n ^ x - n ^ (y - x) * n ^ x = n ^ x := by
        rw [←pow_add, ← pow_add]
        have aux1 : z - x + x = z := by omega
        have aux2 : y - x + x = y := by omega
        rw [aux1, aux2]
        rw [←h]
        simp
      have aux1 : (n ^ (z - x) - n ^ (y - x)) * n ^ x = 
        1 * n ^ x := by
        conv =>
          rhs
          rw [←aux]
        rw [Nat.sub_mul (n ^ (z - x)) (n ^ (y - x)) (n ^ x), Nat.mul_sub]
        simp
      refine Nat.eq_of_mul_eq_mul_right ?_ aux1
      positivity
    have yxge : y - x ≥ 1 := by exact Nat.le_sub_of_add_le' hy
    have zxge1 : z - x ≥ 1 := by 
      calc 
        _ ≥ y - x := by 
          omega
        _ ≥ 1 := yxge
    have ndvd1 : n ∣ n ^ (z - x) := by 
      apply dvd_pow
      simp
      linarith
    have ndvd2 : n ∣ n ^ (y - x) := by
      apply dvd_pow
      simp
      linarith
    have ndvd3 : n ∣ 1 := by
      rw [←eq1]
      exact dvd_sub' ndvd1 ndvd2
    have nle : n ≤ 1 := by 
      exact Nat.le_of_dvd (by positivity) ndvd3
    linarith
    by_cases hx : x > y 
    have eq1 : n ^ (z - y) - n ^ (x - y) = 1 := by 
      have aux : n ^ (z - y) * n ^ y - n ^ (x - y) * n ^ y = n ^ y := by
        rw [←pow_add, ← pow_add]
        have aux1 : z - y + y = z := by omega
        have aux2 : x - y + y = x := by omega
        rw [aux1, aux2]
        rw [←h]
        simp
      have aux1 : (n ^ (z - y) - n ^ (x - y)) * n ^ y = 
        1 * n ^ y := by
        conv =>
          rhs
          rw [←aux]
        rw [Nat.sub_mul, Nat.mul_sub]
        simp
      refine Nat.eq_of_mul_eq_mul_right ?_ aux1
      positivity
    have yxge : x - y ≥ 1 := by exact Nat.le_sub_of_add_le' hx
    have zxge1 : z - y ≥ 1 := by 
      calc 
        _ ≥ x - y := by 
          omega
        _ ≥ 1 := yxge
    have ndvd1 : n ∣ n ^ (z - y) := by 
      apply dvd_pow
      simp
      linarith
    have ndvd2 : n ∣ n ^ (x - y) := by
      apply dvd_pow
      simp
      linarith
    have ndvd3 : n ∣ 1 := by
      rw [←eq1]
      exact dvd_sub' ndvd1 ndvd2
    have nle : n ≤ 1 := by 
      exact Nat.le_of_dvd (by positivity) ndvd3
    linarith
    simp at hy hx
    have xeqy : x = y := by 
      exact Nat.le_antisymm hx hy
    rw [xeqy] at h
    have eq1 : n ^ (z - y) - n ^ (x - y) = 1 := by 
      have aux : n ^ (z - y) * n ^ y - n ^ (x - y) * n ^ y = n ^ y := by
        rw [←pow_add, ← pow_add]
        have aux1 : z - y + y = z := by omega
        have aux2 : x - y + y = x := by omega
        rw [aux1, aux2]
        rw [←h]
        rw [xeqy]
        simp
      have aux1 : (n ^ (z - y) - n ^ (x - y)) * n ^ y = 
        1 * n ^ y := by
        conv =>
          rhs
          rw [←aux]
        rw [Nat.sub_mul, Nat.mul_sub]
        simp
      refine Nat.eq_of_mul_eq_mul_right ?_ aux1
      positivity
    rw [xeqy] at eq1
    simp at eq1
    have zgty : z > y := by 
      by_contra hc
      simp at hc
      have pow_le : n ^ z ≤ n ^ y := by
        exact Nat.pow_le_pow_of_le hn2 hc
      have pos : n ^ y > 0 := by positivity
      linarith
    have zyge : z - y ≥ 1 := by
      exact (Nat.le_sub_iff_add_le' ylez).mpr zgty
    have neq2 : n = 2 := by 
      by_contra hc
      have nge3 : n ≥ 3 := by omega
      have gecontra : n ^ (z - y) ≥ 3 := by 
        calc 
          _ ≥ n ^ 1 := by 
            exact Nat.pow_le_pow_of_le hn2 zyge
          _ = n := by simp 
          _ ≥ 3 := nge3
      linarith
    rw [neq2] at eq1
    have zyex : z - y = 1 := by
      refine (Nat.pow_eq_self_iff (by linarith)).mp eq1
    have zeq :  z = x + 1 := by 
      rw [xeqy, ←zyex]
      omega
    constructor
    exact neq2
    use x
    simp
    constructor
    exact Eq.symm xeqy
    exact zeq
  · -- backward direction
    intro h
    obtain ⟨hn1, k, hx, hy, hz⟩ := h
    rw [hn1, hx, hy, hz]
    omega