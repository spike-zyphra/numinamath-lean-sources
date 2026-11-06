import Mathlib

theorem number_theory_15029 {n m : ℕ} (hnm : m * n = 21^6) (hm : (m % 10) = 7) :
    (n % 10) = 3 := by
  have h1 : (m * n) % 10 = (21^6 : ℕ) % 10 := by
    rw [hnm]
  have h2 : (21^6 : ℕ) % 10 = 1 := by
    norm_num
  rw [h2] at h1
  -- Now we have (m * n) % 10 = 1
  -- And m % 10 = 7
  -- We need to solve for (n % 10)
  have h6 : (m * n) % 10 = 1 := h1
  have h5 : (m % 10) = 7 := hm
  have h8 : (m * n) % 10 = (m % 10) * (n % 10) % 10 := by
    simp [Nat.mul_mod]
    all_goals omega
  rw [h8] at h6
  rw [h5] at h6
  -- Now we have (7 : ℕ) * (n % 10) % 10 = 1
  -- Solve equation to get n % 10 = 3
  -- Now need to solve for (n % 10)
  -- 7 * (n % 10) ≡ 1 (mod 10)
  -- Multiply 7^{-1} ≡ 3 (mod 10) both sides
  -- (n % 10) ≡ 3 * 1 ≡ 3 (mod 10)
  -- Solve to get.
  have h9 : (7 : ℕ) * (n % 10) % 10 = 1 := by
    omega
  -- Now need to solve for (n % 10).
  -- Multiply the inverse of 7 modulo 10, which is 3:
  -- n % 10 = (7^{-1} * 1) % 10 = (3 * 1) % 10 = 3.
  have h10 : n % 10 = 3 := by
    omega
  exact h10