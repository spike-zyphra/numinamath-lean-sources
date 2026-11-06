import Mathlib

lemma l_mul_add_mod_self_right (a b c : Nat) : (a * b + c) % b = c % b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]

/- Mod 11 rule -/
lemma lemma_1
  (a b c : ℕ) (au : a < 10) (bu : b < 10) (cu : c < 10) (apos : a > 0)
  (hn : 11 ∣ a * 100 + b * 10 + c) : (11 : ℤ) ∣ a - b + c  :=
by
  generalize ndef : a * 100 + b * 10 + c = n
  -- split to digits
  have digs : Nat.digits 10 n = [c, b, a] := by
    rw [←ndef]
    rw [Nat.digits_of_two_le_of_pos]
    have : (a * 100 + b * 10 + c) % 10 = c := by
      trans c % 10
      . rw [show a * 100 + b * 10 = (a * 10 + b) * 10 by omega]
        exact l_mul_add_mod_self_right (a * 10 + b) 10 c
      . exact Nat.mod_eq_of_lt cu
    rw [this]
    simp
    rw [Nat.digits_of_two_le_of_pos]
    have : (a * 100 + b * 10 + c) / 10 = a * 10 + b := by
      rw [show a * 100 + b * 10 = (a * 10 + b) * 10 by omega]
      rw [Nat.add_div]
      simp
      have : c / 10 = 0 := by exact Nat.div_eq_of_lt cu
      rw [this]
      have : c % 10 = c := by exact Nat.mod_eq_of_lt cu
      rw [this]
      simp
      assumption
      simp
    rw [this]
    simp
    constructor
    exact Nat.mul_add_mod_of_lt bu
    have : (a * 10 + b) / 10 < 10 := by
      rw [Nat.add_div]
      simp
      have : b / 10 = 0 := by exact Nat.div_eq_of_lt bu
      rw [this]
      have : b % 10 = b := by exact Nat.mod_eq_of_lt bu
      rw [this]
      have : (10 ≤ b) = False := by
        simp
        assumption
      simp [this]
      assumption
      simp
    rw [Nat.digits_of_two_le_of_pos]
    have : (a * 10 + b) / 10 % 10 = (a * 10 + b) / 10 := by
      apply Nat.mod_eq_of_lt
      assumption
    rw [this]
    have : (a * 10 + b) / 10 = a := by
      rw [Nat.add_div]
      simp
      have : b / 10 = 0 := by exact Nat.div_eq_of_lt bu
      rw [this]
      have : b % 10 = b := by exact Nat.mod_eq_of_lt bu
      simp [this]
      assumption
      simp
    rw [this]
    simp
    have : a / 10 = 0 := by exact Nat.div_eq_of_lt au
    rw [this]
    simp
    simp
    simp
    omega
    simp
    simp
    omega
    simp
    omega
  -- Mathlib have this
  have := Nat.modEq_eleven_digits_sum n
  rw [digs] at this
  simp at this
  ring_nf at this
  rw [←ndef] at this
  omega

/- Let $D$ be a positive integer. Suppose $n$ is a three-digit natural number (i.e. $100 \le n \le 999$) such that $n$ is divisible by $D$, and the middle digit of $n$ is equal to the arithmetic mean of its first and last digits. If $D=11$, show that no such $n$ exists. -/
theorem number_theory_635820
  (a b c : ℕ) (au : a < 10) (bu : b < 10) (cu : c < 10) (apos : a > 0)
  (hn : 11 ∣ a * 100 + b * 10 + c)
  (hb : b * 2 = a + c)
  : False :=
by
  have ⟨k, kh⟩ := lemma_1 a b c au bu cu apos hn
  -- Solve the following equations.
  have : b = 11 * k := by
    zify at hb
    have : (a + c : ℤ) = 11 * k + b := by linarith
    rw [this] at hb
    linarith
  have : k = 0 := by
    by_contra h
    have : k > 0 := by omega
    have : b > 11 := by omega
    omega
  subst this
  simp at this kh
  subst this
  simp at kh
  omega
