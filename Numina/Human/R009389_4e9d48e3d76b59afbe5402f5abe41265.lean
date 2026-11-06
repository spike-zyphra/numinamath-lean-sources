import Mathlib
set_option maxHeartbeats 1000000

theorem algebra_88348 :
    {(p, q) : ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ ∃ x₀ x₁ : ℚ, x₀ ≠ x₁ ∧ 3 * x₀ ^ 2 - p * x₀ + q = 0 ∧ 3 * x₁ ^ 2 - p * x₁ + q = 0} = {(5, 2), (7, 2)} := by
  ext ⟨p, q⟩
  constructor
  . rintro ⟨hp, hq, x₀, x₁, hx, hx₀, hx₁⟩
    replace hx₀ : (6 * x₀ - p) ^ 2 = p ^ 2 - 12 * q := by
      linarith only [hx₀]
    replace hx₁ : (6 * x₁ - p) ^ 2 = p ^ 2 - 12 * q := by
      linarith only [hx₁]
    have h₀ : IsSquare ((p ^ 2 - 12 * q : ℤ)) := by
      rw [<-Rat.isSquare_intCast_iff]
      push_cast
      rw [<-hx₀]
      use 6 * x₀ - p
      ring
    obtain ⟨n', h₀⟩ := h₀
    let n := n'.natAbs
    rw [<-Int.natAbs_mul_self', show n'.natAbs = n by rfl, <-pow_two] at h₀
    clear_value n
    clear n'
    have h₁ : p ≥ n := by
      zify
      nlinarith [sq_nonneg (n : ℤ)]
    replace h₀ : (p + n) * (p - n) = 12 * q := by
      zify
      simp [h₁, <-sq_sub_sq]
      omega
    have h₂ : Nat.divisors (12 * q) = {1, 2, 3, 4, 6, 12, q, 2 * q, 3 * q, 4 * q, 6 * q, 12 * q} := by
      rw [Nat.divisors_mul, show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide, Nat.Prime.divisors hq]
      ext d
      simp [Finset.mem_mul]
      aesop
    have h₃ : p - n ∈ Nat.divisors (12 * q) := by
      rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      . rw [<-h₀]
        apply Nat.dvd_mul_left
      . by_contra!
        simp at this
        norm_num [this] at hq
    simp [h₂] at h₃
    have h₄ : 2 ∣ p - n ∧ 2 ∣ p + n := by
      have h₄ : 2 ∣ (p + n) * (p - n) := by
        rw [h₀]
        omega
      have h₅ : 2 ∣ (p + n) + (p - n) := by
        omega
      replace h₄ := (Nat.Prime.dvd_mul Nat.prime_two).mp h₄
      rcases h₄ with (h₄ | h₄)
      . rw [<-Nat.dvd_add_iff_right h₄] at h₅
        tauto
      . rw [<-Nat.dvd_add_iff_left h₄] at h₅
        tauto
    rcases h₃ with (h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃)
    . -- p - n = 1.
      omega
    . -- p - n = 2. We solve to get (p, q) = (7, 2).
      simp [h₃] at h₀
      replace h₃ : p = 3 * q + 1 := by
        omega
      have h₅ : q = 2 := by
        by_contra! h₅
        apply Nat.Prime.odd_of_ne_two hq at h₅
        have h₆ : Even p := by
          rw [h₃]
          apply Odd.add_odd (Odd.mul (by use 1; rfl) h₅) (by use 0; rfl)
        rw [even_iff_two_dvd, Nat.prime_dvd_prime_iff_eq Nat.prime_two hp] at h₆
        omega
      replace h₃ : p = 7 := by
        omega
      simp
      tauto
    . -- p - n = 3.
      omega
    . -- p - n = 4. We solve to get (p, q) = (5, 2).
      simp [h₃] at h₀
      rw [show p + n = 3 * q by omega] at h₄
      have h₅ := (Nat.Prime.dvd_mul Nat.prime_two).mp h₄.2
      norm_num at h₅
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at h₅
      replace h₃ : p = 5 := by
        omega
      simp
      tauto
    . -- p - n = 6.
      simp [h₃] at h₀
      have h₅ : ¬Even q := by
        simp
        apply Nat.Prime.odd_of_ne_two hq (by omega)
      have h₆ : ¬Even (q + 3) := by
        simp
        rw [show q + 3 = p by omega]
        apply Nat.Prime.odd_of_ne_two hp (by omega)
      rw [even_iff_two_dvd] at h₅ h₆
      omega
    . -- p - n = 12.
      simp [h₃] at h₀
      rw [show p + n = q by omega, Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at h₄
      omega
    . -- p - n = q. We solve to get (p, q) = (7, 2).
      simp [h₃, (Nat.Prime.pos hq).ne'] at h₀
      have h₅ : 2 ∣ 12 - q := by
        rw [<-h₀, <-h₃]
        omega
      have h₆ : 2 ∣ q := by
        omega
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at h₆
      replace h₃ : p = 7 := by
        omega
      simp
      tauto
    . -- p - n = 2q. We solve to get (p, q) = (5, 2).
      simp [h₃] at h₀
      replace h₀ : p + n = 6 := by
        nlinarith [Nat.Prime.pos hq]
      replace h₃ : p = q + 3 := by
        omega
      have h₅ : Even q := by
        by_contra! h₅
        simp at h₅
        have h₆ : Even (q + 3) := by
          apply Odd.add_odd h₅ (by use 1; rfl)
        rw [<-h₃, even_iff_two_dvd, Nat.prime_dvd_prime_iff_eq Nat.prime_two hp] at h₆
        omega
      rw [even_iff_two_dvd, Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at h₅
      simp [<-h₅] at h₃
      simp
      tauto
    . -- p - n = 3q.
      simp [h₃] at h₀
      replace h₀ : p + n = 4 := by
        nlinarith [Nat.Prime.pos hq]
      have := Nat.Prime.two_le hq
      omega
    . -- p - n = 4q.
      simp [h₃] at h₀
      replace h₀ : p + n = 3 := by
        nlinarith [Nat.Prime.pos hq]
      have := Nat.Prime.two_le hq
      omega
    . -- p - n = 6q.
      simp [h₃] at h₀
      replace h₀ : p + n = 2 := by
        nlinarith [Nat.Prime.pos hq]
      have := Nat.Prime.two_le hq
      omega
    . -- p - n = 12q.
      simp [h₃] at h₀
      replace h₀ : p + n = 1 := by
        nlinarith [Nat.Prime.pos hq]
      have := Nat.Prime.two_le hq
      omega
  . rintro (⟨hp, hq⟩ | ⟨hp, hq⟩)
    . norm_num
      use 1, 2 / 3
      norm_num
    . norm_num
      use 2, 1 / 3
      norm_num