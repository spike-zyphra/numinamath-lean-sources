import Mathlib
/- Let $a, b, c$ be positive integers such that

$$
\frac{a}{77}+\frac{b}{91}+\frac{c}{143}=1
$$

What is the smallest possible value of $a+b+c$ ? -/
theorem number_theory_610072 : IsLeast {S : ℕ | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a / (77 : ℝ) + b / 91 + c / 143 = 1 ∧ S = a + b + c} 79:= by
  constructor
  -- First part: Prove that a=68, b=10, c=1 is a valid solution with sum 79
  .
    simp
    use 68
    simp
    use 10
    simp
    use 1
    simp
    field_simp
    linarith
  -- Second part: Prove that no smaller solution exists
  .
    simp [lowerBounds]
    intro S a _ b hb c hc h hS
    subst S
    -- Rearrange the equation to get: 13*(a+b+c-77) = 2*b + 6*c
    replace h : 13 * (a + b + c - 77) = 2 * b + 6 * c:= by
      field_simp at h
      suffices 13 * (a + b + c) = 13 * 77 + 2 * b + 6 * c by omega
      rify
      linarith
    -- Show that 13 divides 2*b + 6*c
    have h1 : 13 ∣ 2 * b + 6 * c:= by rw [←h] ; omega
    replace h1 : ∃ k : ℕ, 2 * b + 6 * c = 13 * k:= by exact h1
    rcases h1 with ⟨k, h1⟩
    -- Rewrite as 2*(b + 3*c) = 13*k
    rw [show 2 * b + 6 * c = 2 * (b + 3 * c) by ring] at h1
    -- Show that 2 divides 13*k
    have h2 : 2 ∣ 13 * k:= by rw [←h1] ; omega
    -- Since 2 is prime, either 2 divides 13 or 2 divides k
    have g1 : Nat.Prime 2:= by norm_num
    replace h2 : 2 ∣ 13 ∨ 2 ∣ k:= by exact (Nat.Prime.dvd_mul g1).mp h2
    rcases h2 with h2 | h2
    -- Case 1: 2 divides 13 (impossible)
    .
      omega
    -- Case 2: 2 divides k, so k = 2*t for some natural number t
    .
      replace h2 : ∃ t : ℕ, k = 2 * t:= by exact h2
      rcases h2 with ⟨t, h2⟩
      subst k
      have h3 : t ≥ 1:= by omega
      omega
