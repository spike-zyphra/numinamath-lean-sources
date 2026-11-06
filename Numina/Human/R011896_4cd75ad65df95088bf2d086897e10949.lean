import Mathlib

def IsGood (n : ℕ) : Prop :=
  0 < n ∧ ∀ (a b c : ℝ) (_ : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (_ : a + b + c = 0) (_ : a ^ 3 + b ^ 3 + c ^ 3 = 0), a ^ n + b ^ n + c ^ n = 0

/- 4. $a, b, c$ are not all 0, satisfying $a+b+c=0$, $a^{3}+b^{3}+c^{3}=0$, the positive integer $n$ that makes $a^{n}+b^{n}+c^{n}=0$ always true is called a "good number". Then the number of good numbers among the positive integers not exceeding 2007 is ( ).
(A) 2
(B) 1004
(C) 2006
(D) 2007 -/
theorem algebra_320239 :
    {n : ℕ | n ≤ 2007 ∧ IsGood n}.ncard = 1004 := by
  -- We prove that n is good if and only if n is odd.
  have lem (n : ℕ) : IsGood n ↔ Odd n := by
    constructor
    . -- If n is good and even
      intro ⟨h₀, h⟩
      by_contra! h₁
      simp at h₁
      -- We set a = 0, b = 1, c = -1.
      specialize h (a := 0) (b := 1) (c := -1) (by simp) (by simp) (by norm_num)
      -- So we get 0^n + 1^n + (-1)^n = 0.
      -- But since n is even, we have 0^n + 1^n + (-1)^n = 2, contradiction.
      simp [ne_of_gt h₀, h₁] at h
    . -- If n is odd
      intro h
      -- n is positive
      have h₀ : 0 < n := Odd.pos h
      refine ⟨h₀, fun a b c h₁ h₂ h₃ => ?_⟩
      -- We show that one of a, b, c is 0.
      obtain rfl | rfl | rfl : a = 0 ∨ b = 0 ∨ c = 0 := by
        -- We have 3abc = (a^3 + b^3 + c^3) - (a + b + c)(a^2 + b^2 + c^2 - ab - ac - bc) = 0
        have h₄ : 3 * a * b * c = 0 := by linear_combination (a * b + a * c + b * c - a ^ 2 - b ^ 2 - c ^ 2) * h₂ + h₃
        simp at h₄
        exact or_assoc.mp h₄
      all_goals
        simp at h₂
        -- Then we show that the other two are negatives of each other.
        obtain rfl := eq_neg_of_add_eq_zero_left h₂
        -- Thus we have a^n + b^n + c^n = 0.
        simp [Odd.neg_pow h, ne_of_gt h₀]
  simp [lem]
  -- Now we prove that there are 1004 odd numbers ≤ 2007.
  -- We have a bijection between {i : ℕ | i < 1004} and {n : ℕ | n ≤ 2007 ∧ Odd n}
  apply Set.ncard_eq_of_bijective (f := fun n _ => 2 * n + 1)
  . intro n ⟨hn, i, hi⟩
    exact ⟨i, by omega, hi.symm⟩
  . intro i hi
    simp
    omega
  . intro i j hi hj h
    simpa using h
