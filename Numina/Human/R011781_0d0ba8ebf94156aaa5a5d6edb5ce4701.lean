import Mathlib

/-.Does there exist a prime number whose decimal representation is of the form $3811 \cdots 11$ (that is, consisting of the digits 3 and 8 in that order followed by one or more digits 1 )?-/
theorem number_theory_248298 {a : ℕ → ℕ} (ha : ∀n, a n = Nat.ofDigits 10 (List.replicate n 1 ++ [8, 3])) : ¬∃n, (a n).Prime := by
  simp
  intro n hn₁
  have hn₂ : Nat.digits 10 (a n) = List.replicate n 1 ++ [8, 3] := by
    rw [ha, Nat.digits_ofDigits _ (by omega)]
    simp
    omega
    simp
  -- if a n is prime, then we will get a contradiction
  mod_cases n % 3
  · obtain ⟨k, hk⟩ := show ∃k, n = 3 * k by
      rw [Nat.ModEq] at H
      simp at H
      use n / 3
      omega
    have h₁ : ∀k, 9 * a (3 * k) = (7 * 10^k)^3 - 1 := by
      have : ∀n, a n = 38 * 10^n + Nat.ofDigits 10 (List.replicate n 1) := by
        intro n
        suffices Nat.digits 10 (38 * 10^n + Nat.ofDigits 10 (List.replicate n 1)) = List.replicate n 1 ++ [8, 3] by
          rw [ha, ←this, Nat.ofDigits_digits]
        induction' n with n hn
        · simp
        · simp
          have : (38 * 10 ^ (n + 1) + Nat.ofDigits 10 (List.replicate (n + 1) 1)) % 10 = 1 := by 
            rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
            simp
            rw [List.replicate, Nat.ofDigits_cons]
            simp
          rw [this, List.replicate]
          simp
          have : (38 * 10 ^ (n + 1) + Nat.ofDigits 10 (1 :: List.replicate n 1)) / 10 = 38 * 10 ^ n + Nat.ofDigits 10 (List.replicate n 1) := by
            rw [Nat.ofDigits_cons]
            omega
          rw [this]
          exact hn
      have ha₂ : ∀n, 9 * a n = 342 * 10^n + Nat.ofDigits 10 (List.replicate n 9) := by
        intro n
        rw [this n]
        suffices Nat.ofDigits 10 (List.replicate n 9) = 9 * Nat.ofDigits 10 (List.replicate n 1) by
          rw [this]
          omega
        induction' n with n hn
        · simp
        · rw [List.replicate, List.replicate, Nat.ofDigits_cons, Nat.ofDigits_cons]
          omega
      intro x
      specialize ha₂ (3 * x)
      rw [ha₂]
      have : ∀n, Nat.ofDigits 10 (List.replicate n 9) = 10^n - 1 := by
        intro n
        induction' n with n hn
        · simp
        · rw [List.replicate, Nat.ofDigits_cons, Nat.pow_add_one, hn]
          have : 1 ≤ 10 ^ n := by exact Nat.one_le_pow' n 9
          omega
      rw [this]
      suffices 342 * 10 ^ (3 * x) + 10 ^ (3 * x) = (7 * 10 ^ x)^3 by omega
      rw [show 342 * 10 ^ (3 * x) + 10 ^ (3 * x) = (7 ^ 3) * 10 ^ (3 * x) by ring_nf]
      rw [Nat.mul_pow, mul_comm 3, Nat.pow_mul]
    specialize h₁ k
    set q := 7 * 10^k with hq
    obtain ⟨x, hx⟩ := show ∃x, q - 1 = 3 * x by
      suffices q % 3 = 1 by
        use q / 3
        omega
      rw [hq, Nat.mul_mod, Nat.pow_mod]
      norm_num
    obtain ⟨y, hy⟩ := show ∃y, q^2 + q + 1 = 3 * y by
      suffices (q^2 + q + 1) % 3 = 0 by
        use (q^2 + q + 1) / 3
        omega
      rw [Nat.add_mod]
      suffices (q^2 + q) % 3 = 2 by rw [this]
      rw [Nat.add_mod, hq, Nat.pow_mod, Nat.mul_mod]
      norm_num
      rw [Nat.pow_mod]
      norm_num
      rw [Nat.add_mod, Nat.pow_mod]
      norm_num
    have hxy : a (3 * k) = x * y := by
      suffices 9 * a (3 * k) = 9 * (x * y) by
        simp at this
        exact this
      rw [show 9 * (x * y) = (3 * x) * (3 * y) by ring_nf, ←hx, ←hy]
      have : (q - 1) * (q ^ 2 + q + 1) = q^3 - 1 := by
        rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add, mul_comm, ←Nat.pow_add_one]
        rw [←pow_two]
        simp
        omega
      rw [this]
      exact h₁
    rw [hk, hxy] at hn₁
    absurd hn₁
    apply Nat.not_prime_mul
    · suffices x ≥ 2 by linarith
      suffices q ≥ 7 by omega
      rw [hq]
      simp
      exact Nat.one_le_pow' k 9
    · suffices y ≥ 2 by linarith
      suffices 5 ≤ q ^ 2 + q by omega
      suffices 5 ≤ (q : ℝ)^2 + q by norm_cast at this
      have : (7 : ℝ) ≤ q := by
        norm_cast
        rw [hq]
        simp
        exact Nat.one_le_pow' k 9
      nlinarith
  · -- if n % 3 = 1, then a n is divisible by 3
    suffices 3 ∣ a n by
      rw [Nat.Prime.dvd_iff_eq hn₁ (by simp)] at this
      rw [this, Eq.comm] at hn₂
      simp at hn₂
      revert hn₂
      simp
      have : 1 ∈ List.replicate n 1 ++ [8, 3] := by
        simp
        rw [Nat.ModEq] at H
        simp at H
        omega
      apply ne_of_mem_of_not_mem' this
      simp
    rw [ha, Nat.three_dvd_iff, Nat.digits_ofDigits _ (by omega)]
    simp
    rw [Nat.ModEq] at H
    simp at H
    omega
    simp
    omega
    simp
  · have ha₁ : ∀k, 37 ∣ a (3 * k + 2) := by
      intro k
      induction' k with k hk
      · rw [ha]
        norm_cast
      · have : a (3 * (k + 1) + 2) = 1000 * a (3 * k + 2) + 111 := by
          suffices Nat.digits 10 (1000 * a (3 * k + 2) + 111) = List.replicate (3 * (k + 1) + 2) 1 ++ [8, 3] by
            rw [ha, ←this, Nat.ofDigits_digits]
          simp
          rw [show (1000 * a (3 * k + 2) + 111) % 10 = 1 by omega]
          rw [show (1000 * a (3 * k + 2) + 111) / 10 % 10 = 1 by omega]
          rw [show (1000 * a (3 * k + 2) + 111) / 10 / 10 = 10 * a (3 * k + 2) + 1 by omega]
          simp
          rw [show (10 * a (3 * k + 2) + 1) % 10 = 1 by omega]
          rw [show (10 * a (3 * k + 2) + 1) / 10  = a (3 * k + 2) by omega]
          rw [ha, Nat.digits_ofDigits _ (by omega), show (3 * (k + 1) + 2 = 3 * k + 5) by omega, List.replicate, List.replicate, List.replicate, List.replicate, List.replicate, List.replicate, List.replicate]
          simp
          simp
          simp
        rw [this]
        omega
    obtain ⟨k, hk⟩ := show ∃k, n = 3 * k + 2 by
      rw [Nat.ModEq] at H
      simp at H
      use n / 3
      omega
    specialize ha₁ k
    rw [←hk, Nat.Prime.dvd_iff_eq hn₁ (by simp)] at ha₁
    rw [ha₁, Eq.comm] at hn₂
    simp at hn₂
    revert hn₂
    simp
    have : 1 ∈ List.replicate n 1 ++ [8, 3] := by
      rw [hk]
      simp
    apply ne_of_mem_of_not_mem' this
    simp
