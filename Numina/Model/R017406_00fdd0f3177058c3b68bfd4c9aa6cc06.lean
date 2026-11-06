import Mathlib.Tactic

theorem inequalities_150484 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (n : ℕ) (hn : 0 < n) :
    a^n + b^n + c^n ≥ a * b^(n - 1) + b * c^(n - 1) + c * a^(n - 1) := by
  have h1 : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → x ^ n + y ^ n ≥ x * y ^ (n - 1) + y * x ^ (n - 1) := by
    intro x y hx hy
    have h2 : x ^ n + y ^ n - (x * y ^ (n - 1) + y * x ^ (n - 1)) ≥ 0 := by
      have h3 : x ^ n + y ^ n - (x * y ^ (n - 1) + y * x ^ (n - 1)) = (x - y) * (x ^ (n - 1) - y ^ (n - 1)) := by
        cases n with
        | zero => linarith -- Can't happen as `0 < n` is given.
        | succ n =>
          simp [pow_succ, pow_zero, mul_add, mul_assoc]
          all_goals
            ring
      rw [h3]
      have h4 : (x - y) * (x ^ (n - 1) - y ^ (n - 1)) ≥ 0 := by
        cases n with
        | zero => linarith -- Can't happen as `0 < n` is given.
        | succ n =>
          have h4 : (x - y) * (x ^ (n) - y ^ (n)) ≥ 0 := by
            by_cases h7 : x ≥ y
            · -- x >= y
              have h8 : x ^ (n + 1) ≥ y ^ (n + 1) := by
                apply pow_le_pow_left
                all_goals nlinarith
              have h9 : x ^ (n) ≥ y ^ (n) := by
                apply pow_le_pow_left
                all_goals nlinarith
              nlinarith
            · -- x < y
              have h7' : y ≥ x := by linarith
              have h8 : x ^ (n) ≤ y ^ (n) := by
                apply pow_le_pow_left
                all_goals nlinarith
              nlinarith
          simpa using h4
      linarith
    linarith
  have h2 := h1 a b ha hb
  have h3 := h1 b c hb hc
  have h4 := h1 c a hc ha
  cases n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n =>
    simp [pow_succ, pow_zero] at h2 h3 h4 ⊢
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha 
    ]