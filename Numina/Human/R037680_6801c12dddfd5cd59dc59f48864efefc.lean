import Mathlib

/- If the positive integers $x$ and $y$ are such that both $3 x+4 y$ and $4 x+3 y$ are perfect squares, prove that both $x$ and $y$ are multiples of 7 . -/
theorem number_theory_606224 (x y : ℤ) (hx : x > 0) (hy : y > 0) (h1 : ∃ n, 3 * x + 4 * y = n ^ 2) (h2 : ∃ m, 4 * x + 3 * y = m ^ 2) :
    7 ∣ x ∧ 7 ∣ y := by
  obtain ⟨n, h₁⟩ := h1
  obtain ⟨m, h₂⟩ := h2
  -- Since 3x + 4y and 4x + 3y are perfect squares, 7(x+y) = m² + n².
  have h₃ : 7 ∣ m ^ 2 + n ^ 2 := by
    calc
      7 ∣ 7 * (x + y) := by
        apply Int.dvd_mul_right
      _ = m ^ 2 + n ^ 2 := by
        rw [<-h₁, <-h₂]
        ring
  -- Change h₃ to (m² mod 7 + n² mod 7) mod 7 = 0.
  apply Int.emod_eq_zero_of_dvd at h₃
  rw [Int.add_emod] at h₃
  -- Show that any square modulo 7 is either 0, 1, 2 or 4.
  have h7residue : ∀ a : ℤ, a ^ 2 % 7 = 0 ∨ a ^ 2 % 7 = 1 ∨ a ^ 2 % 7 = 2 ∨ a ^ 2 % 7 = 4 := by
    intro a
    have : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases this with (h | h | h | h | h | h | h)
    <;> simp [h, pow_two, Int.mul_emod, Int.add_emod]
  -- By listing all possibilities, show that m ^ 2 ≡ n ^ 2 ≡ 0 [MOD 7].
  have hmn : (m ^ 2 % 7 = 0) ∧ (n ^ 2 % 7 = 0) := by
    rcases h7residue m with (h1 | h1 | h1 | h1)
    all_goals
      rcases h7residue n with (h2 | h2 | h2 | h2)
      all_goals
        omega
  -- Now we have 7 ∣ m² and 7 ∣ n².
  have hm := Int.dvd_of_emod_eq_zero hmn.1
  have hn := Int.dvd_of_emod_eq_zero hmn.2
  -- Since 7 is a prime, 7 ∣ m and 7 ∣ n.
  have h7m := Int.Prime.dvd_pow (show Nat.Prime 7 by native_decide) hm
  zify at h7m
  simp at h7m
  have h7n := Int.Prime.dvd_pow (show Nat.Prime 7 by native_decide) hn
  zify at h7n
  simp at h7n
  -- Now 7²∣ m² + n²=7(x+y).
  have h₄ : 7 ^ 2 ∣ 7 * (x + y) := by
    calc
      7 ^ 2 ∣ m ^ 2 + n ^ 2 := by
        apply dvd_add
        apply pow_dvd_pow_of_dvd h7m
        apply pow_dvd_pow_of_dvd h7n
      _ = 7 * (x + y) := by
        rw [<-h₁, <-h₂]
        ring
  -- Therefore, 7 ∣ x + y.
  rw [show (7 ^ 2 : ℤ) = 7 * 7 by norm_num] at h₄
  have hxy := Int.dvd_of_mul_dvd_mul_left (show 7 ≠ 0 by norm_num) h₄
  -- On the other hand, 7 ∣ m² - n².
  have h₅ : 7 ∣ m ^ 2 - n ^ 2 := by
    apply dvd_sub
    apply dvd_pow h7m (by norm_num)
    apply dvd_pow h7n (by norm_num)
  -- Therefore, 7 ∣ m² - n² = x - y.
  rw [<-h₂, <-h₁] at h₅
  ring_nf at h₅
  -- Now 7 ∣ x - y and 7 ∣ x + y, we can tidy up to conclude that 7 ∣ x and 7 ∣ y.
  -- Convert divisibility conditions to congruence relations modulo 7.
  rw [Int.dvd_iff_emod_eq_zero] at hxy h₅ ⊢
  rw [Int.dvd_iff_emod_eq_zero]
  -- Prove x ≡ y ≡ 0 (mod 7) by combining the congruences.
  -- Given x + y ≡ 0 (mod 7).
  have h3 : (x + y) % 7 = 0 := by simpa using hxy
  -- Given x - y ≡ 0 (mod 7).
  have h4 : (x - y) % 7 = 0 := by simpa using h₅
  -- Adding the congruences: (x + y) + (x - y) ≡ 2x ≡ 0 (mod 7).
  -- Subtracting the congruences: (x + y) - (x - y) ≡ 2y ≡ 0 (mod 7).
  -- Since 2 and 7 are coprime, conclude x ≡ y ≡ 0 (mod 7).
  omega