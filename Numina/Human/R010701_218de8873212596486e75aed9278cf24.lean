import Mathlib
open Finset

/- How many solutions does the equation \[\frac{(x-1)(x-2)(x-3)\dotsm(x-100)}{(x-1^2)(x-2^2)(x-3^2)\dotsm(x-100^2)} = 0\]have for $x$? -/
theorem algebra_12068 : Set.ncard {x : ℝ | ∏ i ∈ Icc (1 : ℕ) 100, (x - i^2) ≠ 0 ∧ (∏ i ∈ Icc (1 : ℕ) 100, (x - i)) / (∏ i ∈ Icc (1 : ℕ) 100, (x - i^2)) = 0} = 90 := by

  -- We reduce the problem to finding the number of solutions to the equation (x-1)(x-2)(x-3)...(x-100) = 0 that are not solutions to the equation (x-1^2)(x-2^2)(x-3^2)...(x-100^2) = 0.
  have H1 : {x : ℝ | ¬∏ i ∈ Icc (1 : ℕ) 100, ((x - i^2)) = 0 ∧ (∏ i ∈ Icc (1 : ℕ) 100, ((x - i))) / (∏ i ∈ Icc (1 : ℕ) 100, ((x - i^2))) = 0} = {x : ℝ | ¬∏ i ∈ Icc (1 : ℕ) 100, (x - i^2) = 0 ∧ ∏ i ∈ Icc (1 : ℕ) 100, (x - i) = 0} := by
    ext x
    simp
    tauto

  -- A product of terms is zero if and only if one of the terms is zero.
  have H2 : {x : ℝ | ¬∏ i ∈ Icc (1 : ℕ) 100, (x - i^2) = 0 ∧ ∏ i ∈ Icc (1 : ℕ) 100, (x - i) = 0} = {x : ℝ | ¬(∃ i ∈ Icc (1 : ℕ) 100, x - i^2 = 0) ∧ ∃ i ∈ Icc (1 : ℕ) 100, (x - i) = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, prod_eq_zero_iff]

  -- The set of solutions to the equation (x-1)(x-2)(x-3)...(x-100) = 0 is in bijection with the set {1, 2, 3, ..., 100}
  -- The proof is complicated but trivial work
  -- I would not like to comment it line by line
  -- The same for lemma H5
  have H3 : {x : ℝ | ¬(∃ i ∈ Icc (1 : ℕ) 100, x - i^2 = 0) ∧ ∃ i ∈ Icc (1 : ℕ) 100, (x - i) = 0} = map { toFun := ((↑) : ℕ → ℝ), inj' := CharZero.cast_injective } {x ∈ Icc 1 100 | ¬∃ i ∈ Icc (1 :) 100, x = i^2} := by
    ext x
    simp
    constructor <;> intro h
    . obtain ⟨h1, i, ⟨h2, h3⟩⟩ := h
      use i
      rw [sub_eq_zero] at h3
      subst x
      refine ⟨⟨h2, ?_⟩, rfl⟩
      intro j hj1 hj2
      specialize h1 j hj1 hj2
      rw [sub_eq_zero] at h1
      contrapose! h1
      norm_cast
    . obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := h
      constructor
      . intro j hj1 hj2
        specialize hi2 j hj1 hj2
        contrapose! hi2
        rw [sub_eq_zero] at hi2
        norm_cast at hi2
      . use i
        exact ⟨hi1, sub_self _⟩

  -- Tautological lemma
  have H4 : {x ∈ Icc 1 100 | ¬∃ i ∈ Icc (1 :) 100, x = i^2} = Icc 1 100 \ {x ∈ Icc 1 100 | ∃ i ∈ Icc (1 :) 100, x = i^2} := by
    ext x
    simp
    tauto

  -- The set of solutions to the equation (x-1^2)(x-2^2)(x-3^2)...(x-100^2) = 0 (x ∈ [1, 100] ∩ ℕ) is in bijection with the set {1^2, 2^2, 3^2, ..., 10^2}
  have H5 : {x ∈ Icc 1 100 | ∃ i ∈ Icc (1 :) 100, x = i^2} = map { toFun := (· ^ 2), inj' := Nat.pow_left_injective (by norm_num) } (Icc 1 10) := by
    ext x
    simp
    constructor <;> intro h
    . obtain ⟨⟨h1, h2⟩, ⟨i, ⟨h3, _⟩, h4⟩⟩ := h
      subst h4
      use i
      refine ⟨⟨h3, ?_⟩, rfl⟩
      nlinarith
    . obtain ⟨i, ⟨h1, h2⟩, h3⟩ := h
      subst h3
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . nlinarith
      . nlinarith
      . use i
        refine ⟨⟨h1, ?_⟩, rfl⟩
        linarith

  -- Combine the results
  -- The number of solutions to the equation (x-1)(x-2)(x-3)...(x-100) = 0 that are not solutions to the equation (x-1^2)(x-2^2)(x-3^2)...(x-100^2) = 0 is the number of solutions to the equation (x-1)(x-2)(x-3)...(x-100) = 0 minus the number of solutions to the equation (x-1^2)(x-2^2)(x-3^2)...(x-100^2) = 0.
  -- That is 100 - 10 = 90.
  rw [H1, H2, H3, Set.ncard_coe_Finset, Finset.card_map, H4, Finset.card_sdiff (filter_subset _ _), H5, Finset.card_map]
  simp
