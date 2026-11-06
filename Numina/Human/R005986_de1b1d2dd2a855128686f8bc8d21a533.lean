import Mathlib

/- $p$ and $q$ are primes such that the numbers $p+q$ and $p+7 q$ are both squares. Find the value of $p$. -/
theorem number_theory_610971 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h₀ : IsSquare (p + q)) (h₁ : IsSquare (p + 7 * q)) : p = 2 := by
  -- Write p + q = x² and p + 7q = y².
  obtain ⟨x, hx⟩ := h₀
  obtain ⟨y, hy⟩ := h₁
  rw [<-pow_two] at hx hy
  -- Show thta x ≤ y.
  have h₀ : x ≤ y := by
    rw [<-Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num), <-hx, <-hy]
    omega
  -- Subtract the two equations to get 6q = y² - x².
  have h₁ : 6 * q = (y + x) * (y - x) := by
    rw [<-Nat.sq_sub_sq, <-hx, <-hy]
    omega
  rw [show 6 * q = 2 * (3 * q) by ring] at h₁
  -- Show that y + x and y - x are even.
  have h₂ : ¬(Odd (y + x) ∨ Odd (y - x)) := by
    -- Assume not, then they are both odd.
    by_contra! h₂
    cases h₂ with
    | inl h₂ =>
      -- Now y + x is odd, so as y - x.
      have h₃ : Odd (y - x) := by
        rw [show y + x = y - x + 2 * x by omega, Nat.odd_add] at h₂
        rw [h₂]
        simp
      -- Now 2 * (3 * q) is odd, which is a contradiction.
      have h₄ : Odd (2 * (3 * q)) := by
        rw [h₁]
        apply Odd.mul h₂ h₃
      absurd h₄
      simp
    | inr h₂ =>
      -- Now y - x is odd, so as y + x.
      have h₃ : Odd (y + x) := by
        rw [show y + x = y - x + 2 * x by omega, Nat.odd_add]
        simp [h₂]
      -- Now 2 * (3 * q) is odd, which is a contradiction.
      have h₄ : Odd (2 * (3 * q)) := by
        rw [h₁]
        apply Odd.mul h₃ h₂
      absurd h₄
      simp
  -- Now y + x and y - x are both even.
  simp at h₂
  -- Show that 2 ∣ q.
  iterate 2 rw [even_iff_two_dvd] at h₂
  have h₃ : 2 * 2 ∣ 2 * (3 * q) := by
    rw [h₁]
    apply mul_dvd_mul
    exact h₂.1
    exact h₂.2
  apply Nat.dvd_of_mul_dvd_mul_left at h₃
  apply Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) at h₃
  -- Since 2 and q are prime, q = 2.
  rw [Nat.prime_dvd_prime_iff_eq (Nat.prime_two) hq] at h₃
  subst q
  iterate 2 rw [dvd_iff_exists_eq_mul_right] at h₂
  -- Now (y + x) * (y - x) = 12, but they are both even, we can show that y + x = 6 and y - x = 2.
  obtain ⟨⟨n, h₂⟩, ⟨m, h₃⟩⟩ := h₂
  rw [h₂, h₃] at h₁
  replace h₁ : n * m = 3 := by
    linarith
  have h₄ : n > m := by
    -- It suffices to verify that x > 0 and hand the rest to omega.
    have : x > 0 := by
      by_contra!
      simp at this
      simp [this] at hx
    omega
  -- Now n = 3, which means that y + x = 2.
  replace h₄ : n = 3 := by
    have h₄ : n ∣ 3 := by
      rw [<-h₁]
      apply Nat.dvd_mul_right
    apply Nat.Prime.eq_one_or_self_of_dvd at h₄
    cases h₄ with
    | inl h₄ =>
      -- Impossible that n = 1, because n > m.
      have h₅ : m = 0 := by
        omega
      simp [h₅] at h₁
    | inr h₄ =>
      exact h₄
    norm_num
  -- Now y + x = 6, y - x = 2, and p = 2.
  simp [h₄] at h₁
  subst m n
  have h₅ : y = 4 := by
    omega
  subst y
  omega
  norm_num