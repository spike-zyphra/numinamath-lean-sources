import Mathlib

-- we show the mod lemma of pow for ℤ
lemma int.pow_mod (a b: ℤ) (n: ℕ): a ^ n % b = (a % b) ^ n % b := by
   induction' n with n ih
   .
    simp
   .
    rw [show a ^ (n + 1) = a * a ^ n by ring]
    rw [Int.mul_emod]
    rw [ih]
    rw [show (a % b) ^ (n + 1) = (a % b) * (a % b) ^ n by ring]
    set c:= a % b
    set d:= c ^ n
    rw [Int.mul_emod]
    simp
    symm
    apply Int.mul_emod

/-Let $k$ be a positive integer such that $k \equiv 1 \pmod 6$.
Compute $(29^k - 5^k) \pmod 7$. Show that the answer is 3.-/

theorem number_theory_639125 (k: ℕ) (h: k % 6 = 1): (29 ^ k - 5 ^ k) % 7 = (3: ℤ) := by
  rw [Int.sub_emod]
  suffices 29 ^ k % 7 = (1: ℤ) ∧ 5 ^ k % 7 = (5: ℤ) by
     simp [this]
  constructor
  .
    rw [int.pow_mod (29: ℤ) 7 k]
    simp
  .
    replace h: (k + 5) % 6 = 0 := by
      rw [Nat.add_mod]
      simp [h]
    apply Nat.dvd_of_mod_eq_zero at h
    apply exists_eq_mul_right_of_dvd at h
    obtain ⟨m, hm⟩ := h
    have u: 0 < m := by omega
    set q:= m - 1
    replace hm: k = 6 * q + 1 := by
      omega
    rw [hm]
    clear hm
    ring_nf
    rw [Int.mul_emod]
    suffices 5 ^ (q * 6) % 7 = (1: ℤ) by
      simp [this]
    rw [show q * 6 = 6 * q by ring]
    rw [pow_mul]
    rw [int.pow_mod ((5: ℤ) ^ 6) 7 q]
    simp
