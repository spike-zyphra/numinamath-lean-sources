import Mathlib

/- A store normally sells windows at

100\$ each. This week the store is offering one free window for each purchase of four. Dave needs seven windows and Doug needs eight windows. How much will they save if they purchase the windows together rather than separately? -/

theorem algebra_97274 {a b ab : ℕ} {f : ℕ → ℕ } (ha : a = 7) (hb : b = 8) (hab: ab = a + b) (hf: ∀ n: ℕ , f n = 100 * ⌊n/5⌋₊): f ab - (f a + f b) = 100 := by
  -- For n windows the store offers a discount of 100 * ⌊n/5⌋ (f(n))
  -- Substitute with Dave's order (a = 7), Doug's order (b = 8) and with a combined order (ab = 7 + 8)
  rw [hab, ha, hb]
  simp only [hf]
  -- Evaluating the dicount function and simplifying
  norm_num