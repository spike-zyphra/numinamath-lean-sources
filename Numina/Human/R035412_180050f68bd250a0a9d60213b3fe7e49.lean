import Mathlib

/-A palindrome is a positive integer that reads the same backwards as forwards,
such as 82328. What is the smallest 5 -digit palindrome that is a multiple of 99 -/
theorem number_theory_611167: IsLeast {a: ℕ | ∃ x y z: ℕ,(1 ≤ x) ∧ (x ≤ 9) ∧ (y ≤ 9) ∧ (z ≤ 9) ∧
(a = x * 10^4 + y * 10^3 + z * 10^2 + y * 10 + x) ∧ (99 ∣ a)} 54945 := by
  constructor     -- a = xyzyx --
  -- check 54945 is right --
  . simp
    use 5
    simp
    use 4
    simp
    use 9
    simp
    omega

  -- prove the lower bound --
  . intro a
    intro ha
    simp at ha
    obtain ⟨x, hx1,hx2, y, hy, z, hz, ha,dvd⟩ := ha
    have eq: a = 99 * (101 * x + 10 * y + z) + 20 * y + 2 * x + z := by
      simp [ha]
      ring
    rw [eq] at dvd
    have dvd2: 99 ∣ 20 * y + 2 * x + z := by omega
    have up_bound: 20 * y + 2 * x + z ≤ 207 := by   -- upper bound is 207, hence y can only be 0,1,2 --
      nlinarith
    apply exists_eq_mul_right_of_dvd at dvd2
    obtain ⟨k, hk⟩ := dvd2
    have bk: k ≤ 2 := by nlinarith
    have k_eq: k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases k_eq with (k_eq | k_eq | k_eq)
    -- k = 0 --
    . simp [k_eq] at hk
      linarith
    -- k = 1 --
    . simp [k_eq] at hk  -- Then y must be 4 --
      have y_val: y = 4 := by nlinarith
      simp [y_val] at hk
      replace hk: 2 * x + z = 19 := by nlinarith
      nlinarith
    -- k = 2 --
    . simp [k_eq] at hk -- Then y must be 9 --
      nlinarith
