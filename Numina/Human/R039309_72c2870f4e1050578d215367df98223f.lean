import Mathlib

/- Vind alle paren priemgetallen $(p, q)$ waarvoor geldt dat

$$
p\left(p^{2}-p-1\right)=q(2 q+3)
$$ -/
theorem number_theory_605251 :
    {(p, q) : ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ p * (p ^ 2 - p - 1) = q * (2 * q + 3)} = {(13, 31)} := by
  -- Break the goal into two parts.
  ext ⟨p, q⟩
  constructor
  . -- First show that if the condition holds, then (p, q) = (13, 31).
    rintro ⟨hp, hq, h₀⟩
    -- Show that p, q ≥ 2.
    have hp' := Nat.Prime.two_le hp
    have hq' := Nat.Prime.two_le hq
    -- Show that p² ≥ p + 1, and hence p² - p - 1 in ℕ is the same as p² - p - 1 in ℤ.
    have h₁ : p ^ 2 ≥ p + 1 := by
      nlinarith
    have h₂ : (p ^ 2 - p - 1 : ℕ) = (p ^ 2 - p - 1 : ℤ) := by
      simp [Nat.sub_sub, sub_sub, Int.natCast_sub h₁]
    -- First show that p ≠ q.
    have h₃ : p ≠ q := by
      by_contra!
      subst p
      zify at h₀
      rw [h₂] at h₀
      -- Show that q(q - 4)(q + 1) = 0, which is impossible since q is prime.
      replace h₀ : q * (q - 4) * (q + 1 : ℤ) = 0 := by
        linarith
      simp at h₀
      rcases h₀ with (h₀ | h₀) | h₀
      . -- Case q = 0, impossible.
        norm_num [h₀] at hq
      . -- Case q = 4, impossible.
        apply eq_of_sub_eq_zero at h₀
        norm_cast at h₀
        norm_num [h₀] at hq
      . -- Case q = -1, impossible.
        omega
    -- Show that p ∣ 2q + 3.
    have h₄ : p ∣ q * (2 * q + 3) := by
      rw [<-h₀]
      apply Nat.dvd_mul_right
    rw [Nat.Prime.dvd_mul hp, Nat.prime_dvd_prime_iff_eq hp hq] at h₄
    simp [h₃] at h₄
    -- Show that q ∣ p² - p - 1.
    have h₅ : q ∣ p * (p ^ 2 - p - 1) := by
      rw [h₀]
      apply Nat.dvd_mul_right
    rw [Nat.Prime.dvd_mul hq, Nat.prime_dvd_prime_iff_eq hq hp] at h₅
    simp [h₃.symm] at h₅
    -- Using the two divisibility conditions above, show that pq ∣ 3(p² - p - 1) - 2q.
    have h₆ : (p * q : ℤ) ∣ (3 * (p ^ 2 - p - 1) - 2 * q : ℤ) := by
      -- Basically we multiply the two conditions and subtract some multiples of pq.
      have h₆ := Nat.mul_dvd_mul h₄ h₅
      zify at h₆
      rw [h₂] at h₆
      rw [<-@Int.dvd_add_right _ ((2 * p - 2) * (p * q) : ℤ) _ (by apply dvd_mul_left)]
      convert h₆ using 1
      ring
    -- Turn the divisibility conditions to inequalities.
    have h₄' := Nat.le_of_dvd (by omega) h₄
    have h₅' := Nat.le_of_dvd (by zify; rw [h₂]; nlinarith) h₅
    apply Int.le_of_dvd (by linarith) at h₆
    -- Show further that pq ≤ 3p² - 4p by using p ≤ 2q + 3 and h₆.
    replace h₆ : p * q ≤ (3 * p ^ 2 - 4 * p : ℤ) := by
      linarith
    -- Show that 2q + 3 < 6p.
    have h₇ : 2 * q + 3 < 6 * p := by
      zify
      calc
        _ < 2 * (q + 4 : ℤ) := by linarith
        _ ≤ 2 * (3 * p) := by
          -- This is possible since pq ≤ 3p² - 4p implies p(q + 4) ≤ p(3p).
          nlinarith
        _ = 6 * p := by ring
    -- Let 2q + 3 = kp for some k.
    obtain ⟨k, h₄⟩ := h₄
    -- We have 0 < k < 6.
    have hk₀ : 0 < k := by
      nlinarith
    have hk₁ : k < 6 := by
      nlinarith
    -- Now we check all cases of k.
    interval_cases k
    . -- Case k = 1.
      have h₈ : 2 * q + 3 = p := by
        simp [h₄]
      -- Substitute this into the original equation.
      subst p
      rw [mul_comm] at h₀
      simp at h₀
      zify at h₀
      rw [h₂] at h₀
      push_cast at h₀
      -- Factorize to get (4q + 5)(q + 1) = 0. This is impossible.
      replace h₀ : (4 * q + 5) * (q + 1) = 0 := by
        zify
        linarith
      simp at h₀
    . -- Case k = 2.
      have h₈ : 2 * q + 3 = p * 2 := by
        rw [h₄]
      -- Note that the left hand side is odd but the right hand side is even. An easy contradiction.
      omega
    . -- Case k = 3.
      have h₈ : 2 * q + 3 = p * 3 := by
        rw [h₄]
      -- We must have 3 ∣ q.
      have h₉ : 3 ∣ 2 * q := by
        rw [<-Nat.dvd_add_left (show 3 ∣ 3 by rfl), h₈]
        apply Nat.dvd_mul_left
      apply Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) at h₉
      -- This means q = 3, because q is a prime.
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hq] at h₉
      -- Then p = 3 as well, contradictory to our assumption that p ≠ q.
      norm_num [show p = 3 by omega, <-h₉] at h₃
    . -- Case k = 4.
      have h₈ : 2 * q + 3 = p * 4 := by
        rw [h₄]
      -- Note that the left hand side is odd but the right hand side is even. An easy contradiction.
      omega
    . -- Case k = 5.
      have h₈ : 2 * q + 3 = p * 5 := by
        rw [h₄]
      -- Substitute this into the original equation.
      rw [h₈, mul_comm, mul_comm p, <-mul_assoc] at h₀
      simp [show p ≠ 0 by omega] at h₀
      replace h₀ := congr_arg (2 * · + 15) h₀
      simp only [show 2 * (q * 5) + 15 = 5 * (2 * q + 3) by ring, h₈] at h₀
      -- Factorize to get (p - 13)(2p - 1) = 0.
      replace h₀ : (p - 13) * (2 * p - 1 : ℤ) = 0 := by
        zify at h₀
        rw [h₂] at h₀
        linarith
      simp at h₀
      rcases h₀ with (h₀ | h₀)
      . -- Case p = 13, the only solution we want.
        simp
        zify at h₈ ⊢
        exact ⟨by linarith, by linarith⟩
      . -- Case 2p - 1 = 0, impossible.
        omega
  . -- Show that (p, q) = (13, 31) is indeed a valid solution.
    rintro ⟨p, q⟩
    norm_num
