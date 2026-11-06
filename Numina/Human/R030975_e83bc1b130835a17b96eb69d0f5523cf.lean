import Mathlib
/- Find the largest integer $n$ such that $3^{512}-1$ is divisible by $2^{n}$. -/
theorem number_theory_611265 : IsGreatest {n : ℕ | 2 ^ n ∣ 3 ^ 512 - 1} 11:= by
  -- We prove a more general result: for any m ≥ 1, the largest n such that 2^n divides 3^(2^m) - 1 is m+2
  have h1 : ∀ m : ℕ, m ≥ 1 → IsGreatest {n : ℕ | 2 ^ n ∣ 3 ^ (2 ^ m) - 1} (m + 2):= by
    intro n hn
    -- We use induction on n
    induction n, hn using Nat.le_induction with
    -- Base case: n = 1
    | base =>
      constructor
      .
        simp
      .
        simp [upperBounds]
        intro n h
        -- If 2^n divides 3^2 - 1 = 8, then 2^n divides 2^3
        replace h : 2 ^ n ∣ 2 ^ 3:= by simp ; exact h
        exact Nat.pow_dvd_pow_iff_le_right'.mp h
    -- Inductive step: assume the result holds for n, prove it for n+1
    | succ n hn ih =>
      constructor
      .
        simp
        -- Algebraic manipulations to rewrite the expression
        rw [show 2 ^ (n + 1) = 2 ^ n * 2 by ring]
        rw [show 2 ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) by ring]
        rw [show 3 ^ (2 ^ n * 2) = (3 ^ (2 ^ n)) ^ 2 by ring]
        rw [show 1 = 1 ^ 2 by ring]
        -- Use the formula for a^2 - b^2 = (a+b)(a-b)
        rw [Nat.pow_two_sub_pow_two _ _]
        rcases ih with ⟨ih1, _⟩
        simp at ih1
        -- Prove that 3 ≡ 1 (mod 2)
        have g1 : 3 ≡ 1 [MOD 2]:= by rfl
        -- Therefore 3^(2^n) ≡ 1 (mod 2)
        replace g1 : 3 ^ (2 ^ n) ≡ 1 ^ (2 ^ n) [MOD 2]:= by exact Nat.ModEq.pow (2 ^ n) g1
        simp at g1
        -- So 3^(2^n) + 1 ≡ 2 ≡ 0 (mod 2)
        replace g1 : 3 ^ (2 ^ n) + 1 ≡ 1 + 1 [MOD 2]:= by exact Nat.ModEq.add g1 rfl
        simp at g1
        replace g1 : 3 ^ (2 ^ n) + 1 ≡ 0 [MOD 2]:= by exact g1
        -- Which means 2 divides 3^(2^n) + 1
        replace g1 : 2 ∣ 3 ^ (2 ^ n) + 1:= by exact Nat.dvd_iff_mod_eq_zero.mpr g1
        exact Nat.mul_dvd_mul g1 ih1
      .
        simp [upperBounds]
        intro t h
        -- More algebraic manipulations
        rw [show 2 ^ (n + 1) = 2 ^ n * 2 by ring] at h
        rw [show 3 ^ (2 ^ n * 2) = (3 ^ (2 ^ n)) ^ 2 by ring] at h
        rw [show 1 = 1 ^ 2 by ring] at h
        rw [Nat.pow_two_sub_pow_two _ _] at h
        -- Prove that 3^2 ≡ 1 (mod 4)
        have g1 : 3 ^ 2 ≡ 1 [MOD 4]:= by rfl
        -- Therefore (3^2)^(2^(n-1)) ≡ 1 (mod 4)
        replace g1 : (3 ^ 2) ^ (2 ^ (n - 1)) ≡ 1 ^ (2 ^ (n - 1)) [MOD 4]:= by exact Nat.ModEq.pow (2 ^ (n - 1)) g1
        rw [show (3 ^ 2) ^ (2 ^ (n - 1)) = 3 ^ (2 * (2 ^ (n - 1))) by exact Eq.symm (Nat.pow_mul 3 2 (2 ^ (n - 1)))] at g1
        rcases ih with ⟨ih1, ih2⟩
        simp at ih1
        simp [upperBounds] at ih2
        rw [show 2 * 2 ^ (n - 1) = 2 ^ (1 + (n - 1)) by ring] at g1
        rw [show 1 + (n - 1) = n by omega] at g1
        simp at g1
        -- So 3^(2^n) + 1 ≡ 2 (mod 4)
        replace g1 : 3 ^ (2 ^ n) + 1 ≡ 1 + 1 [MOD 4]:= by exact Nat.ModEq.add g1 rfl
        simp at g1
        have g2 : 2 ∣ 4:= by omega
        replace g2 : 3 ^ (2 ^ n) + 1 ≡ 2 [MOD 2]:= by exact Nat.ModEq.symm (Nat.ModEq.of_dvd g2 (id (Nat.ModEq.symm g1)))
        replace g2 : 3 ^ (2 ^ n) + 1 ≡ 0 [MOD 2]:= by exact g2
        -- So 2 divides 3^(2^n) + 1
        replace g2 : 2 ∣ 3 ^ (2 ^ n) + 1:= by exact Nat.dvd_iff_mod_eq_zero.mpr g2
        replace g2 : ∃ s : ℕ, 3 ^ (2 ^ n) + 1 = 2 * s:= by exact g2
        rcases g2 with ⟨s, hs⟩
        -- Prove that 4 does not divide 3^(2^n) + 1
        replace g1 : ¬(4 ∣ 3 ^ (2 ^ n) + 1):= by
          by_contra H
          replace H : 3 ^ (2 ^ n) + 1 ≡ 0 [MOD 4]:= by exact Nat.dvd_iff_mod_eq_zero.mp H
          replace H : 2 ≡ 0 [MOD 4]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm H)) g1)
          simp [Nat.ModEq] at H
        by_contra H
        simp at H
        -- 2 is prime
        have g3 : Nat.Prime 2:= by norm_num
        -- Prove that 2 and s are coprime
        have g4 : Nat.Coprime 2 s:= by
          by_contra H
          replace H : 2 ∣ s:= by exact (Nat.Prime.dvd_iff_not_coprime g3).mpr H
          replace H : 2 * 2 ∣ 2 * s:= by exact Nat.mul_dvd_mul_left 2 H
          rw [←hs] at H
          simp at H
          trivial
        rw [hs] at h
        clear ih1
        rw [show t = 1 + (t - 1) by omega] at h
        rw [show 2 ^ (1 + (t - 1)) = 2 * 2 ^ (t - 1) by ring] at h
        rw [show 2 * s * (3 ^ 2 ^ n - 1) = 2 * (s * (3 ^ 2 ^ n - 1)) by ring] at h
        -- If 2^t divides 2*s*(3^(2^n)-1), then 2^(t-1) divides s*(3^(2^n)-1)
        replace h : 2 ^ (t - 1) ∣ s * (3 ^ 2 ^ n - 1):= by
          suffices ∃ k : ℕ, s * (3 ^ 2 ^ n - 1) = 2 ^ (t - 1) * k by exact this
          replace h : ∃ k : ℕ, 2 * (s * (3 ^ 2 ^ n - 1)) = 2 * 2 ^ (t - 1) * k:= by exact h
          rcases h with ⟨k, hk⟩
          use k
          linarith
        -- Since 2 and s are coprime, 2^(t-1) divides 3^(2^n)-1
        replace h : 2 ^ (t - 1) ∣ 3 ^ 2 ^ n - 1:= by
          replace g4 : Nat.Coprime (2 ^ (t - 1)) s:= by exact Nat.Coprime.pow_left (t - 1) g4
          exact Nat.Coprime.dvd_of_dvd_mul_left g4 h
        specialize ih2 h
        replace ih2 : t ≤ n + 3:= by omega
        linarith
  -- Apply the general result with m = 9 to get the answer for 3^512 - 1
  specialize h1 9 (by omega)
  rw [show 2 ^ 9 = 512 by norm_num] at h1
  rw [show 9 + 2 = 11 by omega] at h1
  exact h1
