import Mathlib

/-
27. N4 (POL) Let $k$ be a fixed integer greater than 1 , and let $m=4 k^{2}-5$. Show that there exist positive integers $a$ and $b$ such that the sequence $\left(x_{n}\right)$ defined by  $$ x_{0}=a, \quad x_{1}=b, \quad x_{n+2}=x_{n+1}+x_{n} \quad \text { for } \quad n=0,1,2, \ldots $$  has all of its terms relatively prime to $m$.
-/
theorem number_theory_25181 (k m : ℤ) (hk: k > 1) (hm : m = 4 * k^2 - 5) : ∃a > 0, ∃b > 0, ∀ x : ℕ → ℤ, (x 0 = a ∧ x 1 = b ∧ ∀ n, x (n+2) = x (n+1) + x n) → ∀ n, IsCoprime (x n) m := by

  -- Set a=1.
  use 1
  norm_num
  
  -- Show existence of b such that $b^2 \equiv b + 1 \mod m$
  have lm : ∃ b, b^2 ≡ b + 1 [ZMOD m] ∧ b > 0:= by
    use 2 * k ^ 2 + k - 2
    constructor
    apply Int.modEq_of_dvd
    rw [Int.dvd_def]
    use -k^2 - k + 1
    rw [hm]
    ring
    nlinarith

  -- Fix this b
  rcases lm with ⟨b,hb,pb⟩
  
  -- Devrive $b$ is coprime with $m$ from the property of $b$.
  have hbm : IsCoprime b m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    let d:ℤ := b.gcd m
    have hdb : d ∣ b := Int.gcd_dvd_left
    have hdm : d ∣ m := Int.gcd_dvd_right
    apply Int.ModEq.dvd at hb
    apply dvd_trans hdm at hb
    have : d ∣ b^2 := by apply dvd_pow hdb; norm_num
    rw [dvd_sub_left this] at hb
    rw [dvd_add_right hdb] at hb
    apply Nat.eq_one_of_dvd_one
    rwa [← Int.ofNat_dvd]

  -- Proceed to the goal.
  use b
  constructor
  · exact pb

  intro x hx₀ hx₁ hx
  
  -- By an induction, show that $\forall n, x_n \equiv b^n \mod m$.
  have lm' (n:ℕ) : x n ≡ b^n  [ZMOD m] := by
    induction n using Nat.strongRecOn
    case ind n ih =>
      exact match n with 
        |0 => by rw [hx₀];rfl
        |1 => by rw [hx₁];congr;simp
        |(k + 2) => by 
          rw [hx] 
          apply Int.ModEq.trans
          show _ ≡ b^(k+1) + b^k [ZMOD m]
          · apply Int.ModEq.add
            repeat apply ih; norm_num
          apply Int.ModEq.trans
          show _ ≡ b^k * (b+1) [ZMOD m]
          · congr
            ring
          apply Int.ModEq.trans
          show _ ≡ b^k * b^2 [ZMOD m]
          · apply Int.ModEq.mul_left
            exact hb.symm
          congr 1
          ring
  
  -- We can finish the proof, using the fact that $b$ is coprime with $m$ then its powers are and then so is $x_n$ since congruent to $b^n$ modulo $m$.
  intro n
  rw [Int.isCoprime_iff_gcd_eq_one]
  let d: ℤ := (x n).gcd m
  have hdx :d ∣ x n := Int.gcd_dvd_left
  have hdm :d ∣ m := Int.gcd_dvd_right
  apply Nat.eq_one_of_dvd_one
  rw [← Int.ofNat_dvd]
  suffices d ∣ 1 by exact this
  suffices d ∣ (b^n).gcd m by 
    rw [Int.isCoprime_iff_gcd_eq_one.mp hbm.pow_left] at this
    exact this
  apply Int.dvd_gcd
  · rw [← dvd_sub_left hdx]
    apply dvd_trans hdm
    exact (lm' n).dvd
  · exact hdm