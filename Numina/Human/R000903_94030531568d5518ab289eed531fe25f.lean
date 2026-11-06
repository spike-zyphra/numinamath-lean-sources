import Mathlib

/-Suppose that the least common multiple of the first $25$ positive integers is equal to $26A7114B4C0$. Find $100 \times A + 10 \times B + C$.-/
theorem number_theory_18998 {A B C : ℕ} {f : ℕ → ℕ}
    (hf : ∀n > 1, f n = Nat.lcm (f (n - 1)) n)
    (hf₁ : f 1 = 1)
    (hA: A ≤ 9) (hB : B ≤ 9) (hC : C ≤ 9)
    (h : f 25 = Nat.ofDigits 10 [0, C, 4, B, 4, 1, 1, 7, A, 6, 2]) :
    100 * A + 10 * B + C = 740 := by

  -- First, we observe that both $4$ and $25$ will divide into the least common multiple. Thus, $100$ will divide into the least common multiple, and so $C = 0$.
  have _100dvd : 100 ∣ f 25 := by
    have _25dvd : 25 ∣ f 25 := by
      rw [hf]; simp
      exact Nat.dvd_lcm_right _ _
      simp
    have _4dvd : 4 ∣ f 25 := by
      rw [hf]; simp
      rw [hf]; simp
      rw [Nat.lcm_comm (f 23), Nat.lcm_assoc 24 (f 23) 25]
      apply Nat.dvd_trans (by norm_num) (Nat.dvd_lcm_left _ _)
      repeat simp
    exact Nat.lcm_dvd _25dvd _4dvd
  have c_eq_zero : C = 0 := by
    have : f 25 ≡ 10 * C [MOD 100] := by
      rw [h, Nat.ofDigits_cons, Nat.ofDigits_cons]
      ring_nf
      nth_rw 2 [show C * 10 = C * 10 + 0 by simp]
      apply Nat.ModEq.add rfl
      apply Nat.mod_eq_zero_of_dvd
      simp
    have : 10 * C ≡ 0 [MOD 100] := by
      apply Nat.ModEq.trans this.symm
      apply Nat.mod_eq_zero_of_dvd _100dvd
    rw [Nat.ModEq] at this
    omega
  rw [c_eq_zero] at h
  rw [c_eq_zero]

  -- Also, we notice that $9$ and $11$ divide into the least common multiple. Thus, the sum of the digits must be divisible by $9$: $$2 + 6 + A + 7 + 1 + 1 + 4 + B + 4 = 25 + A + B = 27,36$$and the alternating sum of the digits must be divisible by $11$ (the divisibility rule for $11$): $$2 - 6 + A - 7 + 1 - 1 + 4 - B + 4 = -3 + A - B = 0, -11.$$It follows that $A+B = 2,11$ and $A - B = 3, -8$. Summing the two equations yields that $2A \in {-6,3,5,14}$, of which only $2A = 14 \Longrightarrow A = 7$ works. It follows that $B = 4$, and the answer is $\boxed{740}$.
  have _9_dvd : 9 ∣ f 25 := by
    repeat first
      | rw [hf₁]; simp
      | rw [Nat.lcm_comm (f 17)]
      | rw [Nat.lcm_assoc 18]
      | rw [hf]; simp
    apply Nat.dvd_trans (by norm_num) (Nat.dvd_lcm_left _ _)
    repeat simp
  rw [h, Nat.nine_dvd_iff, Nat.digits_ofDigits _ (by linarith) _ _ (by simp)] at _9_dvd
  simp at _9_dvd
  have _11dvd : 11 ∣ f 25 := by
    repeat first
      | rw [hf₁]; simp
      | rw [Nat.lcm_comm (f 21)]
      | rw [Nat.lcm_assoc 22]
      | rw [hf]; simp
    apply Nat.dvd_trans (by norm_num) (Nat.dvd_lcm_left _ _)
    repeat simp
  rw [h, Nat.eleven_dvd_iff, Nat.digits_ofDigits _ (by linarith) _ _ (by simp)] at _11dvd
  simp at _11dvd
  omega

  repeat simp; omega
