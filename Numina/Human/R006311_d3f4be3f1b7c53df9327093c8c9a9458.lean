import Mathlib

/- Let $b$ be an integer such that $b > 10$. Let $N_1$ be the number whose representation in base $b$ is $(2, 9, 1, 1)$ (meaning $N_1 = 2 \cdot b^3 + 9 \cdot b^2 + 1 \cdot b^1 + 1 \cdot b^0$) and $N_2$ be the number whose representation in base $b$ is $(1, 3, 9, 2)$ (meaning $N_2 = 1 \cdot b^3 + 3 \cdot b^2 + 9 \cdot b^1 + 2 \cdot b^0$).
Evaluate $N_1 - N_2$. Express your answer as a list of digits in base $b$.
Show that the list of digits, from most significant to least significant, is $(1, 5, b-9, b-1)$. -/
theorem number_theory_635773 (b : ℕ) (hb : 10 < b) (N₁ N₂ : ℕ) (hN₁ : Nat.digits b N₁ = [1, 1, 9, 2]) (hN₂ : Nat.digits b N₂ = [2, 9, 3, 1]) :
    Nat.digits b (N₁ - N₂) = [b - 1, b - 9, 5, 1] := by
  -- Note that `Nat.digits` and `Nat.ofDigits` use little-endian representation. They are inverses of each other.
  -- We compute N₁ and N₂ as a polynomial in b.
  apply_fun Nat.ofDigits b at hN₁ hN₂
  rw [Nat.ofDigits_digits] at hN₁ hN₂
  simp [Nat.ofDigits] at hN₁ hN₂
  -- We show that N₂ ≤ N₁.
  have H₁ : N₂ ≤ N₁ := by nlinarith
  -- We show that N₁ - N₂ is equal to [b - 1, b - 9, 5, 1] in base b.
  have H₂ : N₁ - N₂ = Nat.ofDigits b [b - 1, b - 9, 5, 1] := by
    -- Convert to integers to use the `ring` tactic.
    zify
    -- Simplify the inequality, proving ?x ≤ ?y in expressions ?y - ?x.
    simp [H₁, Nat.ofDigits, show 1 ≤ b by omega, show 9 ≤ b by omega]
    simp [hN₁, hN₂]
    -- It's a ring identity.
    ring
  -- Now we show that the digits are correct.
  -- We need to show each digit is less than b, and the first digit is non-zero.
  rw [H₂, Nat.digits_ofDigits b (show 1 < b by omega) _ (by simp; omega) (by simp)]