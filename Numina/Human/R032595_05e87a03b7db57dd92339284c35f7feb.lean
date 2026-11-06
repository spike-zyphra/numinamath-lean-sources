import Mathlib

open Finset Real Nat

/-Show that any number in row n (for n > 0) is at most2 ^ (n−1)
Remark: any number in row (n+1) can be written as sum of two numbers in row n-/
theorem number_theory_611288 {row: ℕ → Finset ℕ} (h0: row 0 = ∅) (h1: row 1 = {1})
(h: ∀ n: ℕ, n > 0 → ∀ x: ℕ, x ∈ row (n + 1) → ∃ a b: ℕ, a ∈ row n ∧ b ∈ row n ∧ x = a + b):
∀ n: ℕ, n > 0 → ∀ x: ℕ, x ∈ row n → x ≤ 2 ^ (n - 1) := by
  -- prove by induction on n --
  intro n
  intro ne
  induction' n with n hn
  . simp [h0]
  . intro x
    intro hx
    specialize h n
    by_cases r: n = 0
    -- the case n = 0 --
    . simp [r] at hx
      simp [h1] at hx
      rw [hx]
      simp [r]
    -- the case n > 0 --
    . replace r: n > 0 := by omega
      simp [r] at h hn
      specialize h x
      simp [hx] at h
      obtain ⟨a, ha, b, hb,h⟩ := h
      have hn2:= hn
      specialize hn a ha
      specialize hn2 b hb
      rw [h]
      simp
      calc
        a + b ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := by omega
            _ = 2 ^ (n - 1) * 2 := by ring_nf
            _ = 2 ^ n := by apply Nat.two_pow_pred_mul_two; omega
