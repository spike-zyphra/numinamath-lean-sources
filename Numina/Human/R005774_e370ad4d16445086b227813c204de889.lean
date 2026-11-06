import Mathlib

/- One of the receipts for a math tournament showed that 72 identical trophies were purchased for $\$-99.9-$, where the first and last digits were illegible. How much did each trophy cost?-/
theorem number_theory_609859 (x : ℕ) (hx : ∃ a b : ℕ, a ≤ 9 ∧ b ≤ 9 ∧ 72 * (x / (100 : ℚ)) = 100 * a + 99.9 + b / (100 : ℚ)) : x / (100 : ℚ) = 11.11 := by
  -- Simplify the given condition and convert entirely to a problem with integers.
  obtain ⟨a, b, hx⟩ := hx
  field_simp at hx ⊢
  norm_num [add_mul] at hx ⊢
  norm_cast at hx ⊢
  rw [show 100 * a * 100 = 10000 * a by ring] at hx
  -- Show that b = 2 because 8 ∣ 10000a + 9990 + b.
  have h₀ : 8 ∣ 10000 * a + 9990 + b := by
    rw [<-hx.2.2, show 72 = 8 * 9 by norm_num, mul_assoc]
    apply Nat.dvd_mul_right
  replace h₀ : b = 2 := by
    omega
  -- Show that a = 7 because 9 ∣ 10000a + 9990 + b.
  have h₁ : 9 ∣ 10000 * a + 9990 + b := by
    rw [<-hx.2.2, show 72 = 9 * 8 by norm_num, mul_assoc]
    apply Nat.dvd_mul_right
  replace h₁ : a = 7 := by
    omega
  -- Show that x = 1111.
  subst a b
  simp at hx
  omega
