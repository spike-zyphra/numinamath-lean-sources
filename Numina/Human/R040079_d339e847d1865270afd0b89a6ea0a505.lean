import Mathlib

/- How many pairs of positive integers $(x, y)$ have the property that the ratio $x: 4$ equals the ratio $9: y$ ?
(A) 6
(B) 7
(C) 8
(D) 9
(E) 10 -/
theorem algebra_268503 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (x / 4 : ℚ) = 9 / y}.encard = 9 := by
  -- It suffices show that the set is equal to the set of pairs of natural numbers that multiply to 36.
  -- In Mathlib, it is called `Nat.divisorsAntidiagonal`.
  suffices H : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (x / 4 : ℚ) = 9 / y} = Nat.divisorsAntidiagonal 36
  {
    rw [H, Set.encard_coe_eq_coe_finsetCard]
    -- The card of the Finset is computable.
    native_decide
  }
  -- We show that the set is equal to the set of pairs of natural numbers that multiply to 36.
  -- All logically trivial.
  ext ⟨x, y⟩
  simp
  constructor
  . intro ⟨hx, hy, h⟩
    field_simp at h
    norm_cast at h
  . intro h
    have h₀ : x * y > 0 := by simp [h]
    have hx : x > 0 := Nat.pos_of_mul_pos_right h₀
    have hy : y > 0 := Nat.pos_of_mul_pos_left h₀
    refine ⟨hx, hy, ?_⟩
    field_simp
    norm_cast
