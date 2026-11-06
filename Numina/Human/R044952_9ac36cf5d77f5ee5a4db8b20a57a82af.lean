import Mathlib

/-
Show that if a prime number $ p $ divides the product of positive integers $ a_{1}, a_{2}, \ldots, a_{n} $, then there exists at least one integer $ i $ such that $ 1 \leq i \leq n $ and $ p $ divides $ a_{i} $.
-/
theorem number_theory_4554
    (p n : ℕ) (a : ℕ → ℕ)
    (h₀ : Nat.Prime p)
    (h₁ : 1 ≤ n)
    (h₂ : ∀ i, 1 ≤ i ∧ i ≤ n → a i > 0)
    (h₃ : p ∣ ∏ i in Finset.Icc 1 n, a i):
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ p ∣ a i := by

  -- start the induction with n = 0
  induction n with
  | zero =>
    -- this case is impossible because n ≥ 1
    linarith
  | succ n ih =>
    -- continue the induction
    cases n with
    | zero =>
      -- base case : n = 1
      use 1
      simp [dvd_normalize_iff.mp h₃]
    | succ n =>
      -- induction steps : n > 1
      -- express this product as (a_{1} a_{2} \cdots a_{n}) a_{n+1}
      rw [Finset.prod_Icc_succ_top (Nat.le_add_left 1 (n + 1))] at h₃
      rcases (Nat.Prime.dvd_mul h₀).mp h₃ with hc | hc
      -- If $ p $ divides $ a_{1} a_{2} \cdots a_{n} $, then by our induction hypothesis, there exists an integer $ i $ such that $ 1 \leq i \leq n $ and $ p $ divides $ a_{i} $.
      . have t1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
        have t2 : (∀ (i : ℕ), 1 ≤ i ∧ i ≤ n + 1 → a i > 0) := by
          rintro i ⟨hi1, hi2⟩
          exact h₂ i ⟨hi1, Nat.le_add_right_of_le hi2⟩
        let ⟨i, hi1, hi2, hi3⟩ := ih t1 t2 hc
        have : i ≤ n + 1 + 1 := Nat.le_add_right_of_le hi2
        use i
      -- On the other hand, if $ p $ divides $ a_{n+1} $, then we have found an integer $ i = n + 1 $ such that $ p $ divides $ a_{i} $.
      . use (n + 1 + 1)
