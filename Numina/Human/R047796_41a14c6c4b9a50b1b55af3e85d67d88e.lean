import Mathlib

/- Suppose $a$ and $b$ are positive integers such that the units digit of $a$ is $2$, the units digit of $b$ is $4$, and the greatest common divisor of $a$ and $b$ is $6$.

What is the smallest possible value of the least common multiple of $a$ and $b$? -/
theorem number_theory_19015 :
    IsLeast {n | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = n} 108 := by
  unfold IsLeast
  constructor
  -- prove that x=108 exists when a=12, b=24
  . simp
    use 12
    simp
    use 54
    simp
    unfold Nat.lcm
    simp

  -- prove that x=108 is the smallest
  . unfold lowerBounds
    simp
    intros x a _ b _ amod10 bmod10 gcd
    unfold Nat.lcm
    rw [gcd]
    let dvd6 := Nat.gcd_dvd a b
    rw [gcd] at dvd6
    let advd6 := dvd6.1
    let bdvd6 := dvd6.2
    have coprime_3_10: (Nat.Coprime 3 10) := by unfold Nat.Coprime; simp
    have gcdx_3_10: (Nat.xgcd 3 10).1 = -3 := by
      unfold Nat.xgcd Nat.xgcdAux
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.cast_ofNat,
        mul_one, zero_sub, mul_zero, sub_zero]
      unfold Nat.xgcdAux
      simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceMod, Nat.div_one, Nat.cast_ofNat, Int.reduceMul, Int.reduceSub, mul_one, zero_sub, Nat.xgcd_zero_left,
        reduceCtorEq]

    -- use the Chinese Remainder Theorem to calculate the remainder of a modulo 30
    have amod30: (∃ c, 12 + 30 * c = a) := by
      have dvd2_3: (2 * 3 ∣ a) := by simp; exact advd6
      have dvd3: (3 ∣ a) := dvd_of_mul_left_dvd dvd2_3
      have mod3: (a ≡ 0 [MOD 3]) := by rw [Nat.modEq_zero_iff_dvd]; exact dvd3
      have mod10: (a ≡ 2 [MOD 10]) := by unfold Nat.ModEq; rw [amod10];
      have mod30: (a ≡ ↑(Nat.chineseRemainder coprime_3_10 0 2) [MOD 3 * 10]) := Nat.chineseRemainder_modEq_unique coprime_3_10 mod3 mod10
      unfold Nat.chineseRemainder Nat.chineseRemainder' Nat.lcm at mod30
      simp [gcdx_3_10] at mod30
      have mod30' := Nat.mod_eq_of_modEq mod30 (by simp)
      have div_add_mod : a % 30 + 30 * (a / 30) = a := Nat.mod_add_div a 30
      rw [mod30'] at div_add_mod
      exact ⟨a / 30, div_add_mod⟩

    -- use the Chinese Remainder Theorem to calculate the remainder of a modulo 30
    have bmod30: (∃ c, 24 + 30 * c = b) := by
      have dvd2_3: (2 * 3 ∣ b) := by simp; exact bdvd6
      have dvd3: (3 ∣ b) := dvd_of_mul_left_dvd dvd2_3
      have mod3: (b ≡ 0 [MOD 3]) := by rw [Nat.modEq_zero_iff_dvd]; exact dvd3
      have mod10: (b ≡ 4 [MOD 10]) := by unfold Nat.ModEq; rw [bmod10];
      have mod30: (b ≡ ↑(Nat.chineseRemainder coprime_3_10 0 4) [MOD 3 * 10]) := Nat.chineseRemainder_modEq_unique coprime_3_10 mod3 mod10
      unfold Nat.chineseRemainder Nat.chineseRemainder' Nat.lcm at mod30
      simp [gcdx_3_10] at mod30
      have mod30' := Nat.mod_eq_of_modEq mod30 (by simp)
      have div_add_mod : b % 30 + 30 * (b / 30) = b := Nat.mod_add_div b 30
      rw [mod30'] at div_add_mod
      exact ⟨b / 30, div_add_mod⟩

    obtain ⟨ ca, ha ⟩ := amod30
    obtain ⟨ cb, hb ⟩ := bmod30

    -- case analysis on ca and cb
    intro h
    match ca with
    | 0 => {
      simp at ha
      match cb with
      | 0 => {
        -- a=12, b=24
        -- the gcd is 12, which contradicts the condition that the gcd is 6
        simp at hb
        rw [<- ha, <- hb] at gcd
        repeat {unfold Nat.gcd at gcd; simp at gcd}
      }
      | 1 => {
        -- the answer is 108
        simp at hb
        rw [<- ha, <- hb] at h
        simp at h
        rw [<- h]
      }
      | Nat.succ (Nat.succ cb') => {
        -- a=12, b=24+30*cb', x is at least 168
        rw [<- ha, <- hb] at h
        simp at h
        ring_nf at h
        have h := calc x = (168 + (60 * cb')) * 6 / 6 := by rw [<-h]; ring_nf
             _ = 168 + (60 * cb') := by simp
        linarith
      }
    }
    | Nat.succ ca' => {
      -- when ca >= 1, x is at least 168
      simp at ha
      rw [<- ha, <- hb] at h
      ring_nf at h
      have h := calc x = (168 + ca' * 120 + ca' * cb * 150 + cb * 210) * 6 / 6 := by rw [<-h]; ring_nf
        _ = 168 + (ca' * 120 + ca' * cb * 150 + cb * 210) := by simp; ring_nf
      have x_bound : 168 <= x := by rw [h]; exact Nat.le_add_right 168 (ca' * 120 + ca' * cb * 150 + cb * 210)
      linarith
    }
