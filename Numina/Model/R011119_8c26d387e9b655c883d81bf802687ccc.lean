import Mathlib

theorem number_theory_225489:
IsLeast {r | ∃x a b c :ℕ, x = 100*a+10*b+c ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9  ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ r=(x:ℚ)/(a+b+c)} (10.5) := by
  constructor
  · -- Show 10.5 is in the set
    use 189, 1, 8, 9
    norm_num
  · -- Show that 10.5 is the least element in the set
    intro r hr
    rcases hr with ⟨x, a, b, c, hx, ha1, hb1, hc1, ha2, hb2, hc2, hab, hbc, hac, hr⟩
    by_contra h
    push_neg at h
    have hx' : (x : ℚ) = 100 * (a : ℚ) + 10 * (b : ℚ) + (c : ℚ) := by
      exact_mod_cast hx
    have h10 : (a + b + c : ℚ) > 0 := by
      have ha3 : (a : ℚ) > 0 := by
        exact_mod_cast show a > 0 by omega
      have hb3 : (b : ℚ) > 0 := by
        exact_mod_cast show b > 0 by omega
      have hc3 : (c : ℚ) > 0 := by
        exact_mod_cast show c > 0 by omega
      linarith
    have h11 : (x : ℚ) / (a + b + c : ℚ) < (10.5 : ℚ) := by
      linarith [hr, h]
    -- Now we need to show that r = x / (a + b + c) < 10.5 is a contradiction by exhaustive checking.
    -- r = x / (a + b + c) < 10.5 ⇒ x < 10.5 * (a + b + c)
    -- Below we perform exhaustive checking to verify that this is a contradiction.
    have h14 : (x : ℚ) < (10.5 : ℚ) * (a + b + c : ℚ) := by
      have hx15 : (a + b + c : ℚ) > (0 : ℚ) := h10
      have h15 : (x : ℚ) / (a + b + c : ℚ) < (10.5 : ℚ) := h11
      have hx18 : (x : ℚ) = (x : ℚ) / (a + b + c : ℚ) * (a + b + c : ℚ) := by
        field_simp [show (a + b + c : ℚ) ≠ 0 by linarith]
      nlinarith [h15, hx18, hx15]
    -- Now we turn the rational inequality into a natural number inequality.
    -- First we turn h14 into:
    -- (↑x : ℚ) < (10.5 : ℚ) * (↑a + ↑b + ↑c : ℚ)
    -- Then we convert it to:
    -- ↑x < (21 / 2) * (↑a + ↑b + ↑c)
    have h15 : a ≤ 9 := by linarith
    have h16 : b ≤ 9 := by linarith
    have h17 : c ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> interval_cases c
      <;> norm_num [hx', hr] at h h14 ⊢
      <;> omega