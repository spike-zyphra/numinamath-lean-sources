import Mathlib

open Real
/-
Find the range of f(A) = (sin A * (3 * cos A ^ 2 + cos A ^ 4 + 3 * sin A ^ 2 + sin A ^ 2 * cos A ^ 2)) /
  (tan A * (1 / cos A - sin A * tan A)
when A ≠ nπ/2 for any integer n
-/
theorem algebra_608372 {y: ℝ}: y ∈ Set.Ioo 3 4 ↔ ∃ A : ℝ, (∀ n: ℤ, A ≠ n * π / 2) ∧
(sin A * (3 * cos A ^ 2 + cos A ^ 4 + 3 * sin A ^ 2 + sin A ^ 2 * cos A ^ 2))
/ (tan A * (1 / cos A - sin A * tan A)) = y := by

-- we show that f(A) is indeed 3 + (cos A) ^ 2 --
  have simplifier: ∀ x: ℝ, (∀ n: ℤ, x ≠ n * π / 2) →
    (sin x * (3 * cos x ^ 2 + cos x ^ 4 + 3 * sin x ^ 2 + sin x ^ 2 * cos x ^ 2)) /
    (tan x * (1 / cos x - sin x * tan x)) = 3 + (cos x) ^ 2 := by
    intro x hx
    have ne_cos: cos x ≠ 0 := by
      by_contra! ne
      rw [Real.cos_eq_zero_iff] at ne
      obtain ⟨n, h⟩ := ne
      specialize hx (2 * n + 1)
      absurd hx
      norm_cast at h
    have ne_sin: sin x ≠ 0 := by
      by_contra! ne
      rw [Real.sin_eq_zero_iff] at ne
      obtain ⟨n, h⟩ := ne
      specialize hx (2 * n)
      absurd hx
      simp [h]
      nlinarith
    -- simplify the numerator --
    have eq1: 3 * cos x ^ 2 + cos x ^ 4 + 3 * sin x ^ 2 + sin x ^ 2 * cos x ^ 2
    = (3 + cos x ^ 2) * (cos x ^ 2 + sin x ^ 2) := by ring
    have sq_sum:= Real.cos_sq_add_sin_sq x
    rw [eq1]
    rw [sq_sum]
    -- simplify the denominator --
    have eq2: tan x * (1 / cos x - sin x * tan x) = sin x * (1 - sin x ^ 2) / cos x ^ 2  := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      ring
    rw [show (1 - sin x ^ 2) = cos x ^ 2 by rw [←sq_sum]; ring] at eq2
    rw [eq2]
    field_simp

  constructor

  -- the forward direction --
  . intro hy
    simp at hy
    set x:= arccos (sqrt (y - 3)) with hx
    replace hx: y = 3 + (cos x) ^ 2 := by
      have o: cos x = sqrt (y - 3) := by
        rw [hx]
        apply Real.cos_arccos
        . have l: 0 ≤ √(y - 3) := by
            apply Real.sqrt_nonneg
          linarith
        . rw [Real.sqrt_le_one]
          linarith
      rw [o]
      have l: √(y - 3) ^ 2 = y - 3 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      rw [l]
      linarith
    use x
    specialize simplifier x
    have x_ne: ∀ n: ℤ, x ≠ n * π / 2 := by
      by_contra! no
      obtain ⟨n, h⟩ := no
      have sq_sum:= Real.cos_sq_add_sin_sq x
      by_cases v: 2 ∣ n
      . apply exists_eq_mul_right_of_dvd at v
        obtain ⟨k, hk⟩ := v
        simp [hk] at h
        rw [show 2 * ↑k * π / 2 = k * π by ring] at h
        have l: sin x = 0 := by
          rw [Real.sin_eq_zero_iff]
          use k
          simp [h]
        simp only [l] at sq_sum
        replace sq_sum: cos x ^ 2 = 1 := by nlinarith
        simp [sq_sum] at hx
        nlinarith
      . replace v: 2 ∣ n - 1 := by omega
        apply exists_eq_mul_right_of_dvd at v
        obtain ⟨k, hk⟩ := v
        replace hk: n = 2 * k + 1 := by omega
        simp [hk] at h
        have l: cos x = 0 := by
          rw [Real.cos_eq_zero_iff]
          use k
        simp only [l] at sq_sum
        replace sq_sum: cos x ^ 2 = 1 := by nlinarith
        simp [sq_sum] at hx
        nlinarith

    simp [x_ne] at simplifier
    simp [x_ne]
    rw [simplifier]
    simp [hx]

  -- the backward direction --
  . intro h
    obtain ⟨x, h⟩ := h
    specialize simplifier x
    rcases h with ⟨ne,h⟩
    simp only [ne] at simplifier
    rw [simplifier] at h
    clear simplifier
    have boundary: (cos x) ^ 2 ≠ 0 ∧ (cos x) ^ 2 ≠ 1 := by
      constructor
      . by_contra! no
        replace no: cos x = 0 := by nlinarith
        rw [Real.cos_eq_zero_iff] at no
        obtain ⟨n, h⟩ := no
        specialize ne (2 * n + 1)
        absurd ne
        simp [h]
      . by_contra! no
        have sq_sum:= Real.cos_sq_add_sin_sq x
        replace no: sin x ^ 2 = 0 := by nlinarith
        replace no: sin x = 0 := by nlinarith
        rw [Real.sin_eq_zero_iff] at no
        obtain ⟨n, h⟩ := no
        specialize ne (2 * n)
        absurd ne
        rw [← h]
        norm_cast
        simp
        field_simp
        ring
    replace boundary: y ≠ 3 ∧ y ≠ 4 := by
      rw [← h]
      constructor
      . by_contra! no
        absurd boundary.1
        nlinarith
      . by_contra! no
        absurd boundary.2
        nlinarith
    simp
    have ineq:= Real.cos_sq_le_one x
    replace ineq: 3 ≤ y ∧ y ≤ 4 := by
      rw [← h]
      constructor
      . nlinarith
      . nlinarith
    rcases ineq with ⟨l,r⟩
    rcases boundary with ⟨l',r'⟩
    constructor
    . by_contra! no
      absurd l'
      nlinarith
    . by_contra! no
      absurd r'
      nlinarith
    tauto
