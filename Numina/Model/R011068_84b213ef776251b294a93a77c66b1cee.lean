import Mathlib

open Nat

theorem algebra_9222 {a b n : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a < b)
    (hn : Odd n) (h1 : a + b * n = 487) :
    (a = 2 ∧ b = 97 ∧ n = 5) ∨ (a = 2 ∧ b = 5 ∧ n = 97) := by
  have h2 : a % 2 = 0 ∨ b % 2 = 0 := by
    by_contra h9
    push_neg at h9
    have h5 : a % 2 = 1 := by
      omega
    have h6 : b % 2 = 1 := by
      omega
    have h7 : (a + b * n) % 2 = 0 := by
      simp [Nat.add_mod, Nat.mul_mod, h5, h6, show n % 2 = 1 by obtain ⟨k, hk⟩ := hn; omega]
    omega
  rcases h2 with (ha2' | hb2')
  · -- Assume h4: a % 2 = 0
    have ha2 : a = 2 := by
      by_cases ha2 : a > 2
      · -- Assume h5: a > 2
        have h6 : ¬(a).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega)
          all_goals omega
        contradiction
      · -- Assume not a > 2, so a ≤ 2
        interval_cases a <;> norm_num at *
    -- From the equation $a + b \cdot n = 487$, we have $2 + b \cdot n = 487$, so $b \cdot n = 485$
    have h4 : b * n = 485 := by
      rw [ha2] at h1
      nlinarith
    -- Now, we need to get the possible values of $b$, $n$.
    have h5 : b ∣ 485 := by
      use n
      all_goals linarith
    have h6 : b ≤ 485 := by
      exact Nat.le_of_dvd (by norm_num) h5
    have h7 : b = 5 ∨ b = 97 := by
      interval_cases b <;> norm_num at h5 hb h4
      <;> omega
    rcases h7 with (r1 | r2)
    · -- Assume h8: b = 5
      have h8 : n = 97 := by
        nlinarith [h4, r1]
      right
      exact ⟨by linarith, by linarith, by linarith⟩
    · -- Assume h8: b = 97
      have h8 : n = 5 := by
        nlinarith [h4, r2]
      left
      exact ⟨by linarith, by linarith, by linarith⟩
  · -- Assume h4: b % 2 = 0
    have hb2 : b = 2 := by
      by_cases hb2 : b > 2
      · -- Assume hb2: b > 2
        have h6 : ¬(b).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
          all_goals omega
        contradiction
      · -- Assume not b > 2, so b ≤ 2
        interval_cases b <;> norm_num at *
    -- From h: a < b, and hb2: b = 2, we get a < 2
    have ha2 : a < 2 := by
      nlinarith [hb2, h]
    -- But then a < 2, and a is prime, contradiction
    interval_cases a <;> norm_num at ha