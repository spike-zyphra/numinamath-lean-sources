import Mathlib

/-Let $n$ be a positive integer and let $k$ be the number of positive integers less than $2^n$ that are invertible modulo $2^n$. If $2^n\equiv 3\pmod{13}$, then what is the remainder when $k$ is divided by $13$?-/
theorem number_theory_19081 (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hk : k = {x : ℕ | x < 2 ^ n ∧ Nat.Coprime x (2 ^ n)}.encard)
    (h : 2 ^ n ≡ 3 [MOD 13]) : k ≡ 8 [MOD 13] := by
  -- Since $2^n$ is a power of $2$, its only prime factor is $2$. So every odd integer is invertible modulo $2^n$ and every even integer is non-invertible modulo $2^n$. Among the positive integers less than $2^n$, there are precisely $\frac{2^n}{2}=2^{n-1}$ odd integers. Thus, \[k=2^{n-1}\equiv 2^{-1}2^n\equiv 7\cdot 3\equiv 21\equiv \boxed{8}\pmod {13}\]

  -- so, first, we need to prove that set is finite
  have : {x : ℕ | x < 2 ^ n ∧ Nat.Coprime x (2 ^ n)}.encard
       = {x : ℕ | x < 2 ^ n ∧ Nat.Coprime x (2 ^ n)}.ncard := by
    apply Eq.symm (Set.Finite.cast_ncard_eq ?_)
    have : {x : ℕ | x < 2 ^ n}.Finite := by
      exact Set.finite_lt_nat (2 ^ n)
    apply Set.Finite.sep this
  rw [this] at hk
  simp at hk

  -- then, prove k = 2^(n - 1)
  have : k = 2^n / 2 := by
    rw [hk]
    have : 2^n = 2 * (2 ^ (n - 1)) := by
      apply Eq.symm (mul_pow_sub_one ?_ 2)
      linarith
    rw [this]
    simp
    rw [this.symm]
    apply Set.ncard_eq_of_bijective
    case f => exact fun i hi => 2 * i + 1
    simp
    intro a ha₁ ha₂
    use (a - 1)/2
    use (by omega)
    have : a ≠ 0 := by
      intro ha
      rw [ha] at ha₂
      simp at ha₂
      have : n = 0 := by omega
      linarith
    have : 1 ≤ a := by omega
    have : 2 ∣ a - 1 := by
      apply (Nat.modEq_iff_dvd' this).mp
      rw [Nat.ModEq, Nat.ModEq.symm]
      rw [Nat.coprime_pow_right_iff hn a 2] at ha₂
      exact Nat.odd_iff.mp (Nat.Coprime.odd_of_right ha₂)
    rcases this with ⟨c, hc⟩
    rw [hc]
    simp
    rw [hc.symm]
    apply Nat.sub_add_cancel (by linarith)

    simp
    intro i hi
    have : i ≤ 2 ^ (n - 1) - 1 := by omega
    constructor
    · apply lt_of_le_of_lt
      have : 2 * i + 1 ≤ 2 ^ n - 1 := by omega
      exact this
      omega
    · apply Nat.Prime.coprime_pow_of_not_dvd
      norm_num
      simp

    intro i j
    omega


  rw [this]
  -- (2 : ℕ)⁻¹ is not allowed in lean4, so use the define of inverse
  have : 7 * 2 ≡ 1 [MOD 13] := by rfl
  have : 2 ^ n / 2 * (7 * 2) ≡ 2 ^ n / 2 * 1 [MOD 13] := by
    exact Nat.ModEq.mul rfl this
  simp at this
  apply Nat.ModEq.trans this.symm
  have : 2 ^ n / 2 * 14 = 2 ^ n * 7 := by
    have : 2^n = 2 * (2 ^ (n - 1)) := by
      apply Eq.symm (mul_pow_sub_one ?_ 2)
      linarith
    rw [this]
    simp
    linarith
  rw [this]
  have : 2 ^ n * 7 ≡ 3 * 7 [MOD 13] := by
    exact Nat.ModEq.mul h rfl
  apply Nat.ModEq.trans this
  rfl
