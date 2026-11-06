import Mathlib

-- we show a lemma to write Δ as a perfect square
lemma lemma_1 (p q r x: ℤ) (h: p * x ^ 2 + q * x + r = 0): ∃ m: ℤ, 0 ≤ m ∧ q ^ 2 - 4 * p * r = m ^ 2 := by
  set u:= 2 * p * x + q
  set Δ:= q ^ 2 - 4 * p * r
  have t: Δ = u ^ 2 := by
    suffices u ^ 2 - Δ = 0 by linarith
    simp [Δ, u]
    ring_nf
    rw [show p * x * q * 4 + p * r * 4 + p ^ 2 * x ^ 2 * 4 = 4 * p * (p * x ^ 2 + q * x + r) by ring]
    simp [h]
  by_cases v: 0 ≤ u
  .
    use u
  .
    use (- u)
    simp at v
    constructor
    .
      linarith
    .
      nlinarith


/-Given a,b∈Z, and a+b is a root of the equation
x^2 +ax+b=0
Then the maximum possible value of b is-/

theorem algebra_112861: IsGreatest {b: ℤ | ∃ a: ℤ, (a + b) ^ 2 + a * (a + b) + b = 0} 9 := by

  constructor

  -- the forward direction
  .
    simp
    use -6
    norm_num

  -- the backward direction
  .
    intro b h
    simp at h
    obtain ⟨a, h⟩ := h
    replace h: 2 * a ^ 2 + 3 * b * a + (b ^ 2 + b) = 0 := by
      nlinarith

    -- then we apply lemma_1 at h
    have i:= lemma_1 2 (3 * b) (b ^ 2 + b) a h
    obtain ⟨m, hm, i⟩ := i
    replace i: (b - 4 - m) * (b - 4 + m) = 16 := by nlinarith
    have d: (b - 4 - m).natAbs ∈ Nat.divisors 16 := by
      simp
      rw [show (16: ℕ) = (16: ℤ).natAbs by simp]
      rw [Int.natAbs_dvd_natAbs]
      rw [← i]
      simp
    rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by native_decide] at d
    simp at d
    zify at d
    by_cases f: 0 ≤ b - 4 - m
    .
      rw [show |b - 4 - m| = b - 4 - m by apply abs_of_nonneg; omega] at d
      rcases d with d | d | d | d | d
      all_goals simp [d] at i; omega
    .
      rw [show |b - 4 - m| = - (b - 4 - m) by apply abs_of_nonpos; omega] at d
      rcases d with d | d | d | d | d
      .
        replace d: b - 4 - m = -1 := by omega
        simp [d] at i
        omega
      .
        replace d: b - 4 - m = -2 := by omega
        simp [d] at i
        omega
      .
        replace d: b - 4 - m = -4 := by omega
        simp [d] at i
        omega
      .
        replace d: b - 4 - m = -8 := by omega
        simp [d] at i
        omega
      .
        replace d: b - 4 - m = -16 := by omega
        simp [d] at i
        omega