import Mathlib

/- 14. 4.35 ** Proof: For all integers $n>1, \frac{1}{5}\left(2^{4 n+2}+1\right)$ is a composite number. -/
theorem number_theory_138252 (n : ℕ) (hn : 1 < n) :
    ¬Nat.Prime ((2^(4*n+2) + 1)/5) ∧ (2^(4*n+2) + 1)/5 ≠ 1 := by
  and_intros
  -- first prove not prime, prove the following inequality as omega will need this
  . have : 2^(2*n+1) > 2^(n+1) := by
      gcongr 2^?_
      . norm_num
      . omega
    -- express 2^(4*n+2) + 1 as multiplication, due to how nat subtraction works, we have to use calc mode
    have h : 2^(4*n+2) + 1 = (2^(2*n+1) + 2^(n+1) + 1) * (2^(2*n+1) - 2^(n+1) + 1) := by calc
      2^(4*n+2) + 1 = 2^(4*n+2) + 1 + 2^(2*n+2) - 2^(2*n+2) := by exact Eq.symm (Nat.add_sub_self_right _ _)
      _ = (2^(2*n+1) + 1)^2 - (2^(n+1))^2 := by ring_nf
      _ = (2^(2*n+1) + 1 + 2^(n+1)) * (2^(2*n+1) + 1 - 2^(n+1)) := by exact Nat.sq_sub_sq _ _
      _ = _ := by
        congr 1
        . ring
        . omega
    -- 5 ∣ 2^(4*n+2) + 1 by modular arithmetic
    have h5 : 5 ∣ 2^(4*n+2) + 1 := by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
      calc
        ↑(2^(4*n+2) + 1 : ℕ) = (2 : ZMod 5) ^(4*n+2) + 1 := by norm_cast
        _ = (2^4)^n*2^2 + 1 := by rw [← pow_mul, ← pow_add]
        _ = 0 := by
          norm_num
          rw [show (16 : ZMod 5) = 1 by norm_cast]
          norm_num
          norm_cast
    rw [h] at h5
    -- the two factors are both ≥ 25, due to lower bound of n
    have h_lb₁ : 25 ≤ (2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1) := by
      calc
        25 = 2^3 * (2^2 - 1) + 1 := by norm_num
        _ ≤ 2^(n + 1) * (2^n - 1) + 1 := by gcongr <;> omega
        _ = 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1 := by
          rw [Nat.mul_sub]
          congr 2 <;> ring
    have h_lb₂ : 25 ≤ (2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1) := by
      have (a b: ℕ) : a - b + 1 ≤ a + b + 1 := by omega
      linarith [this (2^(2*n+1)) (2^(n+1))]
    -- prove an aux lemma that 5 ∣ b, 25 ≤ a, 25 ≤ b implies a*b is not prime
    have aux {a b : ℕ} (h₁ : 5 ∣ b) (h₂ : 25 ≤ a) (h₃ : 25 ≤ b) : ¬ Nat.Prime (a * b / 5) := by
      rw [Nat.mul_div_assoc a h₁]
      apply Nat.not_prime_mul <;> omega
    rw [h]
    -- now 5 ∣ one of the terms, case work and using aux we get the result
    obtain h5 | h5 := Nat.Prime.dvd_mul (show Nat.Prime 5 by norm_num) |>.mp h5
    . rw [mul_comm]
      exact aux h5 h_lb₁ h_lb₂
    . exact aux h5 h_lb₂ h_lb₁
  -- to prove the value is not 1, just use boounding to show 2^(4*n+2) + 1 ≥ 65
  . suffices 1 < (2^(4*n+2) + 1)/5 by linarith
    have : 2^(4*1+2) + 1 < 2^(4*n+2) + 1 := by
      gcongr
      norm_num
    simp at this
    omega