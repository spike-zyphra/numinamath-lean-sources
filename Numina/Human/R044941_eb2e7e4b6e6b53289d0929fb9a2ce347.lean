import Mathlib

/- (Find the non-zero natural numbers $a$ and $b$ such that $\frac{a^{3} b-1}{a+1}$ and $\frac{b^{3} a+1}{b-1}$ are integers.

) -/
theorem number_theory_101912 {a b : ℕ} (ha : a > 0) (hb : b > 1) :
    (a + 1 ∣ a^3 * b - 1 ∧ b - 1 ∣ b^3 * a + 1) ↔ (a = 2 ∧ b = 2 ∨ a = 1 ∧ b = 3 ∨ a = 3 ∧ b = 3) := by
  constructor
  · intro ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
    -- Show that a^3 * b - 1 = (a + 1) * k and b^3 * a + 1 = (b - 1) * m imply
    -- that (a, b) = (2, 2), (1, 3), or (3, 3).
    -- We have an obvious inequality 1 ≤ a ^ 3 * b (it is useful to translate results from ℕ to ℤ).
    have hineq : 1 ≤ a ^ 3 * b := calc
      1 = 1 ^ 3 * 1 := by norm_num
      _ ≤ a ^ 3 * b := by gcongr; omega
    -- Prove that a + 1 divides b + 1.
    have h1 : a + 1 ∣ b + 1 := by
      zify [hineq] at hk ⊢
      -- Show that b + 1 = (a + 1) * ((a^2 - a + 1) * b - k).
      use (a ^ 2 - a + 1) * b - k
      -- We have (a + 1) * (a^2 - a + 1) * b - (a + 1) * k = (a^3 + 1)*b - (a^3 * b - 1) = b + 1.
      rw [mul_sub, ← hk]
      ring
    -- Prove that b - 1 divides a + 1.
    have h2 : b - 1 ∣ a + 1 := by
      zify [hb] at hm ⊢
      -- Show that a + 1 = (b - 1) * (m - a * (b^2 + b + 1)).
      use  m - a * (b ^ 2 + b + 1)
      -- We have (b - 1) * m - (b - 1) * a * (b^2 + b + 1) = (b^3 * a + 1) - (b^3 - 1) * a = a + 1.
      rw [mul_sub, ← hm]
      ring
    -- We derive that b - 1 divides 2.
    have h3 : b - 1 ∣ 2 := by
      -- b - 1 ∣ a + 1 and a + 1 ∣ b + 1 imply that b - 1 ∣ b + 1.
      have := h2.trans h1
      zify [hb] at this ⊢
      -- b - 1 divides (b + 1) - (b - 1) = 2.
      rw [show (2 : ℤ) = (b + 1) - (b - 1) by linarith]
      exact Int.dvd_sub this (Int.dvd_refl _)
    -- b - 1 divides 2 implies that b - 1 = 1 or b - 1 = 2.
    replace hb : b = 2 ∨ b = 3 := by
      have : b - 1 ∈ (2).divisors := by simp [h3]
      rw [show (2 : ℕ).divisors = {1, 2} from rfl] at this
      simp_all
    cases' hb with hb hb <;> subst b <;> norm_num at h1 h2 ⊢
    -- Consider the case b = 2. We need to show that a = 2.
    -- We have a + 1 ∣ 3 so a + 1 = 3 (a + 1 = 1 is impossible since a > 0).
    · apply Nat.le_of_dvd (by norm_num) at h1
      replace h1 : a ≤ 2 := by omega
      interval_cases a <;> omega
    -- Consider that case b = 3. We need to show that a = 1 or a = 3.
    -- We have a + 1 ∣ 4 so a + 1 = 2 or a + 1 = 4 (a + 1 = 1 is impossible since a > 0).
    · apply Nat.le_of_dvd (by norm_num) at h1
      omega
  · intro h
    -- Show that values (a, b) = (2, 2), (1, 3), (3, 3) work.
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num