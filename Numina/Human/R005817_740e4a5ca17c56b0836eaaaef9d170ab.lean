import Mathlib
/- Find all ordered pairs (a,b) of positive integers such that 2a+1 divides 3b−1 and 2b+1 divides 3a−1.-/

theorem Number_theory_610053: {(a,b): ℤ × ℤ | (1 ≤ a) ∧ (1 ≤ b) ∧ (2 * a + 1 ∣3 * b - 1) ∧ (2 * b + 1 ∣3 * a - 1)} = {(2,2), (12,17),(17,12)} := by
  ext ⟨a,b⟩
  constructor
  . intro x
    simp at x
    simp [x]
    rcases x with ⟨a1,b1,p,q⟩
    replace p: ∃ c: ℤ, (3 * b - 1) = c * (2 * a + 1) := by rw [dvd_iff_exists_eq_mul_left] at p; exact p
    replace q: ∃ d: ℤ, (3 * a - 1) = d * (2 * b + 1) := by rw [dvd_iff_exists_eq_mul_left] at q; exact q
    obtain ⟨c,p⟩ := p
    obtain ⟨d,q⟩ := q
    have c1: 0 ≤ c := by
      by_contra! o
      nlinarith
    have d1: 0 ≤ d := by
      by_contra! o
      nlinarith
    have cd_bound: c * d ≤ 2 := by
      by_contra! o
      replace o: 3 ≤ c * d := by omega
      have contra: 12 * (a * b) ≤ 9 * (a * b) := by
        calc
          12 * (a * b) = 3 * (2 * a) * (2 * b) := by ring
                    _≤ 3 * (2 * a + 1) * (2 * b + 1) := by nlinarith
                    _≤ (c * d) * (2 * a + 1) * (2 * b + 1) := by nlinarith
                    _= (3 * a - 1) * (3 * b - 1) := by simp [p,q];ring
                    _≤ 9 * (a * b) := by nlinarith
      have ab_ne_0: 0 < a * b := by nlinarith
      apply Int.le_of_mul_le_mul_right at contra
      simp at contra
      omega
    have c_ne_0: c ≠ 0 := by
      by_contra! o
      simp [o] at p
      omega
    have d_ne_0: d ≠ 0 := by
      by_contra! o
      simp [o] at q
      omega
    have cd_value: ((c = 1) ∨  (c = 2)) ∧  ((d = 1) ∨ (d = 2)) := by
      replace c1: 1 ≤ c := by omega
      replace d1: 1 ≤ d := by omega
      have c2: c < 3 := by
        by_contra! o
        nlinarith
      have d2: d < 3 := by
        by_contra! o
        nlinarith
      omega
    rcases cd_value with ⟨c_value,d_value⟩
    rcases c_value with j | k
    . rcases d_value with u | v
      . simp [j] at p
        simp [u] at q
        left
        omega
      . simp [j] at p
        simp [v] at q
        omega
    . rcases d_value with u | v
      . simp [k] at p
        simp [u] at q
        omega
      . simp [k] at p
        simp [v] at q
        omega
  . intro x
    simp at x
    simp [x]
    rcases x with p | q | r
    . simp [p]
    . simp [q]
      omega
    . simp [r]
      omega