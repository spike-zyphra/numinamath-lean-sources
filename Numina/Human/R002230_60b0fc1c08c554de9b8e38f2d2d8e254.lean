import Mathlib

/- Prove that for every non-negative integer $n$ there exist integers $x, y, z$ with $gcd(x, y, z) = 1$, such that $x^2 + y^2 + z^2 = 3^{2^n}$.(Poland) -/
-- 1.3 hour so far.
-- restarted at 9:45 ended 11:40
theorem number_theory_74910 (n : ℕ) :
    ∃ x y z : ℤ, Int.gcd (Int.gcd x y) z = 1 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 ^ (2 ^ n) := by

  -- It suffices to prove that there exist integers $a$ and $b$ such that
  -- $gcd(a, b) = 1$ and $2a^2 + b^2 = 3^{2^n}$.
  suffices ∃ a b : ℤ, Int.gcd a b = 1 ∧ 2 * a ^ 2 + b ^ 2 = 3 ^ (2 ^ n) by
    obtain ⟨a, b, h₁, h₂⟩ := this
    -- Set $x$ and $y$ to $a$ and $z$ to $b$.
    use a, a, b
    simp [h₁]
    -- We need to show that $gcd(|a|, b) = 1$.
    -- $a ^ 2 + a ^ 2 + b ^ 2 = 3 ^ {2 ^ n}$.
    constructor
    . -- To show that $gcd(|a|, b) = 1$, we consider two cases:
      -- the case with $a ≥ 0$ and the case with $a < 0$.
      by_cases abs : a ≥ 0
      . -- Kimina fails with pass@16
        have : |a| = a := by apply abs_of_nonneg abs
        rw [this]
        exact h₁
      . simp at abs
        have : |a| = -a := by apply abs_of_neg abs
        rw [this]
        simp [h₁]
    . -- Simple algebra shows that $a ^ 2 + a ^ 2 + b ^ 2 = 3 ^ {2 ^ n}$
      rw [← h₂]
      ring

  -- We now prove by induction on $n$ that there exist integers $a$ and $b$
  -- such that $gcd(a, b) = 1$ and $2a^2 + b^2 = 3^{2^n}$.
  induction n with
  | zero =>
      -- When $n = 0$, set $a$ and $b$ to 1 and the base case follows from
      -- a direct calculation.
      use 1, 1
      norm_num
  | succ n ih =>
      -- For the induction step, we first establish that
      -- if $c$ is a natural number and $a$ and $b$ are integers, then
      -- $c$ divides the gcd of $a$ and $b$ iff $c$ divides $a$ and $c$ divides $b$.
      have dvd_gcd_iff {a b : Int} {c : Nat} : c ∣ Int.gcd a b ↔ (c : Int) ∣ a ∧ (c : Int) ∣ b := by
        have dvd_coe_gcd {a b c : Int} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (gcd a b : Int) :=
          Int.ofNat_dvd_right.2 (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.2 ha) (Int.natAbs_dvd_natAbs.2 hb))
        have dvd_coe_gcd_iff {a b c : Int} : c ∣ (Int.gcd a b : Int) ↔ c ∣ a ∧ c ∣ b :=
          ⟨fun h => ⟨Int.dvd_trans h (gcd_dvd_left _ _), Int.dvd_trans h (gcd_dvd_right _ _)⟩,
           fun ⟨ha, hb⟩ => dvd_coe_gcd ha hb⟩
        rw [← Int.ofNat_dvd,dvd_coe_gcd_iff]

      -- By the induction hypothesis, we have integers $x$ and $y$
      -- satisfying $gcd(x, y) = 1$ and $2x^2 + b^2 = 3^{2^n}$.
      obtain ⟨x, y, hx, hy⟩ := ih

      -- Then, with $a = 2xy$ and $b = 2x^2 - y^2$, we obtain
      -- that $gcd(a, b) = 1$ and $2a^2 + b^2 = 3^{2^{n+1}}$,
      -- thus completing the induction step.
      use (2 * x * y), (2 * x ^ 2 - y ^ 2)

      -- We claim that $(2x ^ 2 - y^2)^2 + 2(2xy)^2 = 3^{2^{n+1}}$.
      -- This can be obtained via simple algebra and using the induction hypothesis.
      have claim : (2 * x ^ 2 - y ^ 2) ^ 2 + 2 * (2 * x * y) ^ 2 = 3 ^ 2 ^ (n + 1) := by
        rw [pow_add, pow_one, pow_mul, ← hy]
        ring
      constructor
      . -- To show that $gcd(2xy, 2x^2 - y^2) = 1$, we proceed by contradiction.
        by_contra g
        -- Assume that $gcd(2xy, 2x^2 - y^2)$ is not $1$.
        -- Note that there is a prime $p$ so that $p$ divides $2xy$ and $p$ divides $2x^2-y^2$.
        have : ∃ p, Nat.Prime p ∧ (p : ℤ) ∣ 2 * (x * y) ∧ (p : ℤ) ∣ 2 * x ^ 2 - y ^ 2 := by
          -- Simply take $p$ to be the smallest prime factor of the $gcd(2xy, 2x^2 - y^2)$.
          set p := ((2 * x * y).gcd (2 * x ^ 2 - y ^ 2)).minFac
          use p
          constructor
          . exact Nat.minFac_prime g
          . have : p ∣ (2 * x * y).gcd (2 * x ^ 2 - y ^ 2) := by exact Nat.minFac_dvd ((2 * x * y).gcd (2 * x ^ 2 - y ^ 2))
            rw [dvd_gcd_iff] at this
            rw [← mul_assoc]
            exact this
        obtain ⟨p, hp, dvdxy, dvdfs⟩ := this

        -- We divide into two cases: The case when the prime $p$ is 2
        -- and the case when $p$ is not 2.
        by_cases h : p = 2
        . -- Since $p$ divides $2xy$, $p$ divides $(2xy)^2$
          have h₁ : (p : ℤ) ∣ (2 * (x * y)) ^ 2 := by
            rw [pow_two]
            exact Dvd.dvd.mul_right dvdxy (2 * (x * y))
          -- Since $p$ divides $2x^2-y^2$, $p$ divides $(2x^2-y^2)^2$
          have h₂ : (p : ℤ) ∣ (2 * x ^ 2 - y ^ 2) ^ 2 := by
            rw [pow_two]
            exact Dvd.dvd.mul_right dvdfs (2 * x ^ 2 - y ^ 2)
          -- Hence, $p$ divides $3^{2^{n+1}}$ since by the claim
          -- $3^{2^{n+1}}=(2x^2-y^2)^2+2(2xy)^2$
          have h₃ : (p : ℤ) ∣ 3 ^ 2 ^ (n + 1) := by
            rw [← claim]
            refine (Int.dvd_add_right h₂).mpr ?_
            exact Dvd.intro ((2 * x * y) ^ 2) (congrFun (congrArg HMul.hMul (congrArg Nat.cast h)) ((2 * x * y) ^ 2))
          rw [h] at h₃
          -- But $3^{2^{n+1}}$ is odd.
          have : Odd (3 ^ 2 ^ (n + 1)) := by refine Odd.pow ?_; decide
          -- $p$ is 2 and cannot divide $3^{2^{n+1}}$, and we have a contradiction
          revert this
          norm_cast at h₃
          simp
          exact (even_iff_exists_two_nsmul (3 ^ 2 ^ (n + 1))).mpr h₃
        . -- Now consider the case when $p$ prime and not equal to 2.
          -- Then $p$ is odd
          have hOdd : Odd p := by apply Nat.Prime.odd_of_ne_two hp h

          -- Since $p$ divides $2xy$, $p$ is odd gives $p$ divides $xy$.
          have claim1 : (p : ℤ) ∣ x * y := by
            apply Int.Prime.dvd_mul' hp at dvdxy
            obtain g | g := dvdxy
            . have : ¬(p : ℤ) ∣ 2 := by
                norm_cast
                refine (Nat.Prime.coprime_iff_not_dvd hp).mp ?_
                exact Nat.coprime_two_right.mpr hOdd
              contradiction
            . exact g

          -- Since $p$ is prime, either $p$ divides $x$ or $p$ divides $y$.
          have claim2 : (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y := by exact Int.Prime.dvd_mul' hp claim1

          obtain hdvd | hdvd := claim2
          . -- Suppose that $p$ divides $x$.
            -- Then $p$ divides $2x^2$.
            have : (p : ℤ) ∣ 2 * x ^ 2 := by
              rw [pow_two, ← mul_assoc]
              exact Dvd.dvd.mul_left hdvd (2 * x)

            -- Since $p$ divides $2x^2-y^2$, we must have $p$ divides $y^2$.
            have h₀ : ↑p ∣ y ^ 2 := by exact (Int.dvd_iff_dvd_of_dvd_sub dvdfs).mp this

            -- Thus, $p$ divides $y$ as $p$ is prime.
            have h₁ : ↑p ∣ y  := by exact Int.Prime.dvd_pow' hp h₀

            -- So, we have both $p$ divides $x$ and $p$ divides $y$.
            -- We have that $p$ divides $gcd(x,y)$.
            have : p ∣ Int.gcd x y := by
              rw [dvd_gcd_iff]
              exact ⟨ hdvd, h₁⟩

            -- But $gcd(x,y) = 1$. This is impossible.
            rw [hx] at this
            revert this
            simp
            exact Nat.Prime.ne_one hp
          . -- Now, suppose that $p$ divides $y$.
            -- Then, $p$ divides $y^2$.
            have : (p : ℤ) ∣ y ^ 2 := by
              rw [pow_two]
              exact Dvd.dvd.mul_right hdvd y

            -- Since $p$ divides $2x^2-y^2$, we must have $p$ divides $2x^2$.
            have h₀ : (p : ℤ) ∣ 2 * x ^ 2 := by exact (Int.dvd_iff_dvd_of_dvd_sub dvdfs).mpr this

            -- Hence, $p$ divides $x^2$ since $p$ is odd and cannot divide 2.
            have h₁ : (p : ℤ) ∣ x ^ 2 := by
              apply Int.Prime.dvd_mul' hp at h₀
              obtain g | g := h₀
              . have : p = 2 := by
                  norm_cast at g
                  rw [Nat.dvd_prime Nat.prime_two] at g
                  obtain g' | g' := g
                  . aesop
                  . exact g'
                simp [this] at h
              . exact g

            -- Thus, $p$ divides $x$ as $p$ is prime.
            have h₂ : (p : ℤ) ∣ x := by exact Int.Prime.dvd_pow' hp h₁

            -- So, we have both $p$ divides $x$ and $p$ divides $y$.
            -- We have that $p$ divides $gcd(x,y)$.
            have : p ∣ Int.gcd x y := by
              rw [dvd_gcd_iff]
              aesop

            -- But $gcd(x,y) = 1$. This is impossible.
            rw [hx] at this
            revert this
            simp
            exact Nat.Prime.ne_one hp
      . -- This is basically the claim we showed above.
        rw [add_comm]
        exact claim