import Mathlib

/- Find all pairs of positive integers $(a, b)$ such that $a-b$ is a prime and $a b$ is a perfect square. Answer: Pairs $(a, b)=\left(\left(\frac{p+1}{2}\right)^{2},\left(\frac{p-1}{2}\right)^{2}\right)$, where $p$ is a prime greater than 2 .-/
theorem number_theory_605716 :
    {(a, b) : ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < a - b ∧ Nat.Prime (a - b) ∧ ∃ c, a * b = c ^ 2} = {(a, b) : ℕ × ℕ | ∃ p, Nat.Prime p ∧ 2 < p ∧ (a, b) = (((p + 1) / 2) ^ 2, ((p - 1) / 2) ^ 2)} := by
  -- Break the goal into two parts.
  ext ⟨a, b⟩
  simp
  apply Iff.intro
  . -- First show that the condition implies the set of solutions.
    rintro ⟨h₀, h₁, h₂, h₃, ⟨c, h₄⟩⟩
    -- Let p = a - b.
    let p := a - b
    -- Show that p is a prime.
    have h₅ : Nat.Prime p := by
      simp [p, h₃]
    use p, h₅
    -- We have a = b + p.
    have h₆ : a = b + p := by
      omega
    -- Put a = b + p into h₄.
    rw [h₆] at h₄
    -- We have (2b + p)² = (2c)² + p².
    replace h₄ : (2 * b + p) ^ 2 = (2 * c) ^ 2 + p ^ 2 := by
      linarith
    -- Show that 2b + p ≥ 2c.
    have h₇ : 2 * b + p ≥ 2 * c := by
      rw [ge_iff_le, <-Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num)]
      omega
    -- We have p² = (2b + p)² - (2c)² = (2b + p + 2c)(2b + p - 2c).
    have h₈ : p ^ 2 = (2 * b + p + 2 * c) * (2 * b + p - 2 * c) := by
      rw [<-Nat.sq_sub_sq, h₄, Nat.add_comm, Nat.add_sub_cancel]
    -- Show that 2b + p + 2c is a divisor of p².
    have h₉ : 2 * b + p + 2 * c ∈ (p ^ 2).divisors := by
      simp [Nat.divisors]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . -- Show that 1 ≤ 2b + p + 2c.
        by_contra!
        simp at this
        simp [this.1, this.2] at h₃
        omega
      . -- Show that 2b + p + 2c ≤ p².
        apply Nat.lt_add_one_of_le
        apply Nat.le_of_dvd
        . by_contra!
          simp at this
          norm_num [this] at h₅
        . rw [h₈]
          exact Nat.dvd_mul_right _ _
      . -- Show that 2b + p + 2c ∣ p².
        rw [h₈]
        exact Nat.dvd_mul_right _ _
    -- Show that 2b + p - 2c is a divisor of p².
    have h₁₀ : 2 * b + p - 2 * c ∈ (p ^ 2).divisors := by
      simp [Nat.divisors]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . -- Show that 1 ≤ 2b + p - 2c.
        by_contra!
        simp at this
        simp [this] at h₈
        omega
      . -- Show that 2b + p - 2c ≤ p².
        apply Nat.lt_add_one_of_le
        apply Nat.le_of_dvd
        . by_contra!
          simp at this
          norm_num [this] at h₅
        . rw [h₈]
          exact Nat.dvd_mul_left _ _
      . -- Show that 2b + p - 2c ∣ p².
        rw [h₈]
        exact Nat.dvd_mul_left _ _
    -- Show that (2b + p + 2c) and (2b + p - 2c) are both powers of p.
    rw [Nat.mem_divisors_prime_pow h₅] at h₉ h₁₀
    obtain ⟨m, ⟨hc, h₉⟩⟩ := h₉
    obtain ⟨n, ⟨hd, h₁₀⟩⟩ := h₁₀
    -- Now m + n = 2.
    have h₁₁ : p ^ (m + n) = p ^ 2 := by
      rw [Nat.pow_add, <-h₉, <-h₁₀, <-h₈]
    apply Nat.pow_right_injective (Nat.Prime.two_le h₅) at h₁₁
    -- Show that n < m.
    have h₁₂ : n < m := by
      rw [<-@Nat.pow_lt_pow_iff_right p, <-h₉, <-h₁₀]
      have : c > 0 := by
        by_contra!
        simp at this
        simp [this] at h₄
        omega
      omega
      exact Nat.Prime.one_lt h₅
    -- Show that n = 0 and m = 2.
    replace h₁₂ : n = 0 := by
      omega
    simp [h₁₂] at h₁₁
    subst m n
    -- Sum up two equations to get 4b + 2p = p² + 1.
    have h₁₃ : 4 * b + 2 * p = p ^ 2 + p ^ 0 := by
      omega
    -- Show that p ≠ 2.
    have h₁₄ : p ≠ 2 := by
      by_contra!
      -- Assume on the contrary that p = 2, then b = 1 and c = 0.
      simp [this] at h₉
      have h₁₄ : b = 1 := by
        omega
      have h₁₅ : c = 0 := by
        omega
      -- Contradiction.
      simp [this, h₁₄, h₁₅] at h₈
    replace : p > 2 := lt_of_le_of_ne (Nat.Prime.two_le h₅) h₁₄.symm
    simp [this]
    clear this
    -- Show that p is odd.
    have h₁₅ := Nat.Prime.odd_of_ne_two h₅ h₁₄
    -- Show that p + 1 and p - 1 are even.
    have h₁₆ : Even (p + 1) := by
      apply Odd.add_odd (Nat.Prime.odd_of_ne_two h₅ h₁₄) (by norm_num)
    have h₁₇ : Even (p - 1) := by
      rw [show p + 1 = p - 1 + 2 by omega, Nat.even_add] at h₁₆
      rw [h₁₆]
      norm_num
    -- Write p + 1 = 2x and p - 1 = 2y.
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at h₁₆ h₁₇
    obtain ⟨x, h₁₆⟩ := h₁₆
    obtain ⟨y, h₁₇⟩ := h₁₇
    rw [h₁₆, h₁₇]
    iterate 2 rw [mul_comm, Nat.mul_div_cancel _ (by norm_num)]
    -- Show that (a, b) = (x², y²).
    replace h₁₃ : 4 * b = (2 * y) ^ 2 := by
      rw [<-h₁₇]
      suffices 4 * b + 2 * (p - 1) + 1 ^ 2 = (p - 1) ^ 2 + 2 * (p - 1) + 1 ^ 2 by
        omega
      rw [Nat.mul_sub, add_assoc, <-Nat.sub_add_comm, <-Nat.add_sub_assoc, <-Nat.add_assoc, h₁₃, <-Nat.mul_sub, <-mul_one (2 * (p - 1)), <-add_sq, Nat.sub_add_cancel]
      simp
      all_goals
        omega
    replace h₁₄ : 4 * a = (2 * x) ^ 2 := by
      rw [h₆, mul_add, h₁₃, <-h₁₆, <-h₁₇]
      suffices (p - 1) ^ 2 + 2 * (p - 1) * 2 + 2 ^ 2 = (p + 1) ^ 2 by
        omega
      rw [<-add_sq]
      simp
      rw [Nat.sub_add_cancel (by omega)]
    norm_num [mul_pow] at h₁₃ h₁₄
    tauto
  . -- Show that (((p - 1) / 2)², ((p + 1) / 2)²) is indeed solutions to the conditions.
    rintro ⟨p, h₀, h₁, h₂, h₃⟩
    -- Show that p + 1 and p - 1 are even.
    have h₄ : Even (p + 1) := by
      apply Odd.add_odd (Nat.Prime.odd_of_ne_two h₀ (h₁.ne')) (by norm_num)
    have h₅ : Even (p - 1) := by
      rw [show p + 1 = p - 1 + 2 by omega, Nat.even_add] at h₄
      rw [h₄]
      norm_num
    -- Write p + 1 = 2x and p - 1 = 2y.
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at h₄ h₅
    obtain ⟨x, h₄⟩ := h₄
    obtain ⟨y, h₅⟩ := h₅
    rw [h₄, mul_comm, Nat.mul_div_cancel _ (by norm_num)] at h₂
    rw [h₅, mul_comm, Nat.mul_div_cancel _ (by norm_num)] at h₃
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    . -- Show that 0 < a.
      by_contra!
      replace this : x ^ 2 = 0 := by omega
      simp at this
      simp [this] at h₄
    . -- Show that 0 < b.
      by_contra!
      replace this : y ^ 2 = 0 := by omega
      simp at this
      omega
    . -- Show that 0 < a - b.
      by_contra!
      rw [h₂, h₃, Nat.pow_le_pow_iff_left (by norm_num)] at this
      apply Nat.mul_le_mul_left 2 at this
      omega
    . -- Show that a - b is a prime.
      rw [h₂, h₃, Nat.sq_sub_sq]
      suffices (x + y) * (x - y) = p by
        rw [this]
        exact h₀
      rw [<-@Nat.mul_left_cancel_iff (2 * 2) (by norm_num)]
      rw [mul_assoc, mul_comm, mul_assoc, mul_assoc, mul_comm _ 2, <-mul_assoc, mul_add, Nat.mul_sub, <-h₄, <-h₅, add_comm, add_comm p 1, <-add_assoc, Nat.sub_add_cancel (by omega), <-Nat.Simproc.add_sub_le _ (by omega), add_comm _ 1, <-add_assoc, Nat.add_sub_cancel]
      ring
    . -- Show that ab is a perfect square.
      use x * y
      rw [h₂, h₃]
      ring
