import Mathlib

/-Let $b$ be a natural number such that $b > 4$. Let $N$ be the natural number defined by $N = 1 \cdot b^3 + 2 \cdot b^2 + 4 \cdot b + 2$.
Show that the base $b$ representation of $N$ (when $N$ is calculated in base 10 and then converted to base $b$) is the list of digits $[2, 4, 2, 1]$.-/
theorem Number_Theory_636732 {b : ℕ} (hb : b > 4) (N : ℕ) (hN : N = 1 * b^3 + 2 * b^2 + 4 * b + 2) :
  Nat.digits b N = [2, 4, 2, 1] := by
  rw [hN]
  -- Prove that each digit is less than b
  have h2 : 2 < b := by linarith [hb]
  have h4 : 4 < b := by linarith [hb]
  have h1 : 1 < b := by linarith [hb]

  -- Use digits_ofDigits
  rw [← Nat.digits_ofDigits b h1 [2, 4, 2, 1] (by simp [h2, h4, h1])]
  congr 1
  simp [Nat.ofDigits]
  ring
  decide
