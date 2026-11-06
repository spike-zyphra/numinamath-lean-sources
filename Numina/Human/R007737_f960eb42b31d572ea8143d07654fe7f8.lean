import Mathlib

/-If the least common multiple of $A$ and $B$ is $1575$, and the ratio of $A$ to $B$ is $3:7$, then what is their greatest common divisor?-/
theorem number_theory_22769 {A B : ℕ} (h₀ : Nat.lcm A B = 1575) (h₁ : A * 7 = B * 3) :
    Nat.gcd A B = 75 := by
  -- Since the ratio of $A$ to $B$ is $3:7$, there is an integer $k$ for which $A=3k$ and $B=7k$. Moveover, $k$ is the greatest common divisor of $A$ and $B$, since 3 and 7 are relatively prime. Recalling the identity $\mathop{\text{lcm}}[A,B]\cdot\gcd(A,B)=AB$, we find that $1575k=(3k)(7k),$ which implies $k=1575/21=\boxed{75}$.
  obtain ⟨k, hk₁⟩ := show 3 ∣ A by
    have dvd₁ : 3 ∣ A * 7 := by
      rw [h₁]
      simp
    apply Nat.Coprime.dvd_of_dvd_mul_right ?_ dvd₁
    norm_num
  have hk₂ : B = 7 * k := by linarith
  have : Nat.lcm A B * Nat.gcd A B = A * B := by
    rw [mul_comm]
    exact Nat.gcd_mul_lcm _ _
  rw [h₀] at this
  nth_rw 2 [hk₁, hk₂] at this
  -- Prove that gcd A B = k
  have hk₃ : Nat.gcd A B = k := by
    rw [hk₁, hk₂, Nat.gcd_eq_iff]
    simp
    intro c hc₁ hc₂
    -- we have c ∣ 3 * k and c ∣ 7 * k, prove that c ∣ k
    obtain ⟨p, hp⟩ := hc₁
    obtain ⟨q, hq⟩ := hc₂
    obtain ⟨p', hp'⟩ := show 3 ∣ p by
      have : 3 * q = 7 * p := by
        have : 3 * q * c = 7 * p * c := by linarith
        simp at this
        obtain (r | r) := this
        · -- r: 3 * q = 7 * p
          exact r
        · -- r: c = 0
          rw [hk₁, hp, r] at h₀
          simp at h₀
      omega
    use p'
    rw [hp'] at hp
    linarith
  rw [hk₃]
  rw [hk₃, ←mul_assoc] at this
  simp at this
  obtain (r | r) := this
  · -- 1575 = 3 * k * 7
    linarith
  · -- k = 0
    rw [hk₁, r] at h₀
    simp at h₀
