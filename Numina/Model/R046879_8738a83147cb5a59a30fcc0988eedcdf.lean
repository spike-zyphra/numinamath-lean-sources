import Mathlib

/-- A triangle with integer sides a, b, c is a "Linglong Triangle" if the height on one side
    is exactly the sum of the heights on the other two sides. -/
def IsLingLongTriangle (a b c : ℕ) : Prop :=
  -- Triangle inequality must hold
  a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧
  -- Heights relationship: assuming h_a = h_b + h_c
  (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c

theorem number_theory_318004_1 : ∃ a b c : ℕ, IsLingLongTriangle a b c := by
  -- We use the example from the solution: a=6, b=10, c=15
  use 6, 10, 15
  
  -- Prove all conditions one by one and combine them
  have h1 : 6 > 0 := by norm_num
  have h2 : 10 > 0 := by norm_num
  have h3 : 15 > 0 := by norm_num
  have h4 : 6 + 10 > 15 := by norm_num
  have h5 : 6 + 15 > 10 := by norm_num
  have h6 : 10 + 15 > 6 := by norm_num
  have h7 : (1 : ℚ) / 6 = (1 : ℚ) / 10 + (1 : ℚ) / 15 := by norm_num
  
  -- Combine all the conditions
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem number_theory_318004_2 {a b c : ℕ} (h : IsLingLongTriangle a b c) : 
  ∃ n : ℕ, a^2 + b^2 + c^2 = n^2 := by 
  rcases h with ⟨ha, hb, hc, h₁, h₂, h₃, h⟩
  have h4 : (a : ℚ) > (0 : ℚ) := by 
    exact_mod_cast ha
  have h5 : (b : ℚ) > (0 : ℚ) := by 
    exact_mod_cast hb
  have h6 : (c : ℚ) > (0 : ℚ) := by 
    exact_mod_cast hc
  -- Let $X = \frac{b*c}{a} ? No that's wrong, from h' cross multiply we get b*c=a*(b+c)$
  have eq1 : (b : ℚ) * (c : ℚ) = (a : ℚ) * ((b : ℚ) + (c : ℚ)) := by
    field_simp at h ⊢
    nlinarith
  have eq2 : (b : ℕ) * (c : ℕ) = (a : ℕ) * ((b : ℕ) + (c : ℕ)) := by
    exact_mod_cast eq1
  have h7 : a ≤ b + c := by 
    nlinarith
  use b + c - a 
  have h9 : a^2 + b^2 + c^2 = (b + c - a) ^ 2 := by 
    cases Nat.le.dest h7 with
    | intro k hk =>
      have h9 : a + k = b + c := by 
        omega 
      have h10 : a = b + c - k := by 
        omega 
      rw [show (b + c - a) = k by omega] 
      rw [show a = b + c - k by omega] 
      nlinarith [sq_nonneg (b - c : ℤ), sq_nonneg ((b : ℤ) - (c : ℤ)), sq_nonneg (k : ℤ), 
        eq2, 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
  exact h9