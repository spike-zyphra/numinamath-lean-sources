import Mathlib

/- How many solutions does the equation:  $$ [\frac{x}{20}]=[\frac{x}{17}] $$  have over the set of positve integers? $[a]$  denotes the largest integer that is less than or equal to  $a$ . -/
theorem number_theory_8858 :
  Set.ncard {x : ℕ | 0 < x ∧ ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋} = 56 := by

  -- Lemma 1:
  -- If x is a real number such that ⌊x / 20⌋ = ⌊x / 17⌋, then x < 120.
  have lm1 (x : ℝ) (h : ⌊x / 20⌋ = ⌊x / 17⌋) : x < 120 := by
    -- We have ⌊x / 20⌋ = ⌊x / 17⌋, so |x / 20 - x / 17| < 1.
    replace h := Int.abs_sub_lt_one_of_floor_eq_floor h

    -- Simplify the LHS we get |x * (-3 / 340)| < 1.
    field_simp at h
    ring_nf at h

    -- Thus x * (-3 / 340) > -1 and we are done.
    replace h := neg_lt_of_abs_lt h
    linarith

  -- Lemma 2:
  -- If x and y are natural numbers, then ⌊(x / y : ℝ)⌋ = x / y. (x and y are seen as members of ℤ in the RHS)
  have lm2 (x y : ℕ) : ⌊(x / y : ℝ)⌋ = x / y := by
    -- Easily solved by using the lemmas in the library:
    -- 0 ≤ a → ↑⌊a⌋₊ = ⌊a⌋
    -- ⌊↑m / ↑n⌋₊ = m / n for m, n : ℕ
    have h : (x / y : ℝ) >= 0 := by positivity
    rw [← Int.natCast_floor_eq_floor h, Nat.floor_div_eq_div]
    simp

  -- Lemma 3:
  -- If x is a natural number, then ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋ if and only if (x / 20 : ℤ) = (x / 17 : ℤ).
  have lm3 (x : ℕ) : ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋ ↔ (x / 20 : ℤ) = (x / 17 : ℤ) := by
    -- The proof is trivial by using lemma 2.
    have t1 : ⌊(↑x / 20 : ℝ)⌋ = x / 20 := lm2 x 20
    have t2 : ⌊(↑x / 17 : ℝ)⌋ = x / 17 := lm2 x 17
    rw [t1, t2]


  -- Step 1: Use lemma 3 to simplify the set S to P := {x : ℕ | 0 < x ∧ (↑(x / 20) : ℤ) = ↑(x / 17)}.
  -- This is to make the predicate calculable.
  let S := {x : ℕ | 0 < x ∧ ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋}
  let P := {x : ℕ | 0 < x ∧ (↑(x / 20) : ℤ) = ↑(x / 17)}
  have h1 : S = P := by
    ext x
    simp [S, P]
    intro _
    exact lm3 x

  -- Step 2: Construct a finset T := {n | n < 120} ∩ P such that:
  -- 1. T = P = S, this can be proved by showing that every element in P is less than 120, which is done by lemma 1.
  -- 2. The cardinality of T is now computable.
  let T := (Finset.range 120).filter (λ x => x ∈ P)
  -- We want to prove Set.ncard S = T.card.
  have h2 : Set.ncard S = T.card := by
    -- Suffices to prove P = ↑T.
    rw [h1]
    convert Set.ncard_coe_Finset T

    -- Prove P = ↑T by using lemma 1 and lemma 3.
    ext x
    simp [P, T]
    intro _ h
    rw [← lm3] at h
    exact Nat.cast_lt_ofNat.1 (lm1 x h)
  -- Now S can be replaced by T.
  rw [h2]

  -- Step 3: Prove the cardinality of T is 56.
  -- This is done by calculation.
  rfl
