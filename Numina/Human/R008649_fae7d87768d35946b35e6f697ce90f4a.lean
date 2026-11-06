import Mathlib

/-
The two digits in Jack's age are the same as the digits in Bill's age, but in reverse order. In five years Jack will be twice as old as Bill will be then. What is the difference in their current ages?
(A) 9(B) 18(C) 27(D) 36(E) 45
-/

theorem algebra_95384 (x y a b : ℕ) (h1 : x < 100) (hx : x = 10 * a + b) (hy : y = 10 * b + a) (h2 : x + 5 = 2 * (y + 5)): x - y = 18 := by
  -- Prove 8*a=19*b+5
  rw [hx, hy, mul_add, mul_add, ← mul_assoc, (by norm_num: 2*10 = 20), (by norm_num: 2*5 = 10)] at h2
  have hab : 8 * a = 19 * b + 5 := by linarith
  -- Esablish formula for valid natural number solutions of b
  have mod_eq : (19 * b + 5) % 8 = 0 := by
    rw [← hab, Nat.mul_mod 8 a 8, Nat.mod_self 8, zero_mul, Nat.zero_mod]
  -- Get an upper bound for b
  have b_lt_5 : b < 5 := by
    by_contra h
    have : 5 ≤ b := Nat.not_lt.mp h
    have : 19 * 5 ≤ 19 * b := Nat.mul_le_mul_left 19 this
    have : 95 ≤ 19 * b := by norm_num at this; exact this
    have : 8 * a ≥ 95 + 5 := by
      rw [hab]
      linarith
    have : 8 * a ≥ 100 := by norm_num at this; exact this
    have : a ≥ 13 := by
      have : 8 * a ≥ 8 * 13 := by
        linarith [this]
      exact Nat.le_of_mul_le_mul_left this (by norm_num)
    linarith

  -- Since b is a natural number, b < 5 and b ≠ 0 means b ∈ {1, 2, 3, 4}
  -- Case b = 1
  have case_b1 : b = 1 → a = 3 := by
    intro hb1
    rw [hb1] at hab
    linarith

  -- Case b = 2
  have case_b2 : b = 2 → False := by
    intro hb2
    rw [hb2] at mod_eq
    contradiction

  -- Case b = 3
  have case_b3 : b = 3 → False := by
    intro hb3
    rw [hb3] at mod_eq
    contradiction

  -- Case b = 4
  have case_b4 : b = 4 → False := by
    intro hb4
    rw [hb4] at mod_eq
    contradiction

  -- Conclude b = 1 by elimination
  have : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
    omega
  cases this with
  | inl b1 => rw [hx, hy, case_b1 b1, b1];
  | inr more_cases =>
    cases more_cases with
    | inl b2 => exfalso; exact case_b2 b2
    | inr more_cases =>
      cases more_cases with
      | inl b3 => exfalso; exact case_b3 b3
      | inr b4 => exfalso; exact case_b4 b4