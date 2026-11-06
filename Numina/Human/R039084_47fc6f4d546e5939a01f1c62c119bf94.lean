import Mathlib

def is_interesting (n : ℕ) := ∃ p q, p.Prime ∧ q.Prime ∧ p * q = n

/- Let's call a positive integer "interesting" if it is a product of two (distinct or equal) prime numbers. What is the greatest number of consecutive positive integers all of which are "interesting"? -/
theorem number_theory_240510 :
    IsGreatest {k | ∃ m, ∀ i ∈ Finset.range k, is_interesting (m + i)} 3 := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- First show that there exists 3 consecutive interesting numbers.
    use 33
    intro i hi
    interval_cases i
    . -- We have 33 = 3 * 11.
      use 3, 11
      norm_num
    . -- We have 34 = 2 * 17.
      use 2, 17
      norm_num
    . -- We have 35 = 5 * 7.
      use 5, 7
      norm_num
  . -- Show that there cannot be more than 3 consecutive numbers.
    intro k m h₀
    by_contra!
    -- There must be some multiple of 4 in the range.
    let n := (m + 3) / 4
    have h₁ : m + 3 = 4 * n + (m + 3) % 4 := by
      rw [Nat.div_add_mod]
    -- We have 3 - (m + 3) % 4 < k.
    have : 3 - (m + 3) % 4 < k := by
      calc
        3 - (m + 3) % 4 ≤ 3 := by omega
        _ < k := this
    have h₂ := h₀  (3 - (m + 3) % 4) this
    clear this
    rw [<-Nat.add_sub_assoc (by omega), h₁, Nat.add_mod (4 * n)] at h₂
    simp at h₂
    -- Now we have 4 * n interesting, which means that n = 1.
    have h₃ : n = 1 := by
      by_contra!
      rw [ne_iff_lt_or_gt] at this
      cases this with
      | inl this =>
        -- We eliminate the case n < 1.
        rw [show n = 0 by omega] at h₂
        obtain ⟨p, q, hp, hq, h₄⟩ := h₂
        simp at h₄
        obtain h₄ | h₄ := h₄
        . subst p
          norm_num at hp
        . subst q
          norm_num at hq
      | inr this =>
        -- We consider the case n > 1.
        have h₃ := h₂
        simp [is_interesting] at h₂
        obtain ⟨p, hp, q, hq, h₄⟩ := h₂
        have h₅ := Nat.ne_one_iff_exists_prime_dvd.mp this.ne'
        obtain ⟨r, ⟨hr, h₅⟩⟩ := h₅
        rw [dvd_iff_exists_eq_mul_right] at h₅
        obtain ⟨c, h₅⟩ := h₅
        -- Now we have pq = (4c)r, where p, q and r are primes.
        rw [h₅, mul_comm _ c, <-mul_assoc] at h₄
        -- We have r = p or q.
        have h₅ : r ∣ p * q := by
          rw [h₄]
          apply dvd_mul_left
        rw [Nat.Prime.dvd_mul] at h₅
        iterate 2 rw [Nat.prime_dvd_prime_iff_eq] at h₅
        obtain h₅ | h₅ := h₅
        . -- If r = p, 4c = q.
          subst r
          rw [mul_comm, Nat.mul_right_cancel_iff (by by_contra!; simp at this; norm_num [this] at hp)] at h₄
          absurd hq
          rw [h₄]
          apply Nat.not_prime_mul (by norm_num)
          -- If c = 1, it means that q = 4 is a prime, which is not the case.
          by_contra! h₆
          norm_num [h₄, h₆] at hq
        . -- If r = q, 4c = p.
          subst r
          rw [Nat.mul_right_cancel_iff (by by_contra!; simp at this; norm_num [this] at hq)] at h₄
          absurd hp
          rw [h₄]
          apply Nat.not_prime_mul (by norm_num)
          -- If c = 1, it means that p = 4 is a prime, which is not the case.
          by_contra! h₆
          norm_num [h₄, h₆] at hp
        assumption'
    -- Now n = 1, but it means that some consecutive 4 interesting numbers contains 4, which is impossible.
    have h₄ : 1 ≤ m := by
      omega
    have h₅ : m ≤ 4 := by
      omega
    interval_cases m
    . -- If m = 1, we observe that 1 is not interesting.
      specialize h₀ 0
      simp [is_interesting, show 0 < k by positivity] at h₀
      norm_num at h₀
    . -- If m = 2, we observe that 2 is not interesting.
      specialize h₀ 0
      simp [is_interesting, show 0 < k by positivity] at h₀
      obtain ⟨p, hp, q, hq, h₀⟩ := h₀
      have h₀' : p ∣ 2 := by
        rw [<-h₀]
        apply Nat.dvd_mul_right
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_two)] at h₀'
      simp [h₀'] at h₀
      norm_num [h₀] at hq
    . -- If m = 3, we observe that 3 is not interesting.
      specialize h₀ 0
      simp [is_interesting, show 0 < k by positivity] at h₀
      obtain ⟨p, hp, q, hq, h₀⟩ := h₀
      have h₀' : p ∣ 3 := by
        rw [<-h₀]
        apply Nat.dvd_mul_right
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_three)] at h₀'
      simp [h₀'] at h₀
      norm_num [h₀] at hq
    . -- If m = 4, we observe that 5 is not interesting.
      specialize h₀ 1
      simp [is_interesting, show 1 < k by omega] at h₀
      obtain ⟨p, hp, q, hq, h₀⟩ := h₀
      have h₀' : p ∣ 5 := by
        rw [<-h₀]
        apply Nat.dvd_mul_right
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_five)] at h₀'
      simp [h₀'] at h₀
      norm_num [h₀] at hq
