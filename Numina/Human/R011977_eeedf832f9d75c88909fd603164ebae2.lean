import Mathlib

/- Lemma 1: For any integer x and y, 121 ∣ x ^ 2 + y ^ 2 if and only if 11 ∣ x ∧ 11 ∣ y -/
def lemma_1 {x y : ℤ} : 121 ∣ x ^ 2 + y ^ 2 ↔ 11 ∣ x ∧ 11 ∣ y := by
  constructor
  . intro h
    -- We have 11 is a prime number.
    have inst : Fact (Nat.Prime 11) := ⟨by decide⟩
    -- The Legendre symbol of -1 modulo 11 is -1, in other words, -1 is not a quadratic residue modulo 11.
    have h₁ : legendreSym 11 (-1) = -1 := by
      simp [legendreSym.at_neg_one (show 11 ≠ 2 by simp)]
    -- 11 divides x ^ 2 + y ^ 2.
    have h₂ : ↑(11 : ℕ) ∣ x ^ 2 + y ^ 2 := dvd_trans (by norm_num) h
    -- We use the important property of the Legendre symbol:
    -- If p is a prime number and the Legendre symbol of a modulo p is -1,
    -- Then p ∣ x ^ 2 - a * y ^ 2
    -- Since a is not a quadratic residue modulo 11.
    have H := legendreSym.prime_dvd_of_eq_neg_one (p := 11) (a := -1) h₁ (x := x) (y := y) (by simpa)
    simpa using H
  . -- The other direction is trivial.
    rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    ring_nf
    exact dvd_add (Int.dvd_mul_left (a ^ 2) 121) (Int.dvd_mul_left (b ^ 2) 121)

/- Man ermittle die Anzahl aller Zahlen der Form $x^{2}+y^{2}(x, y \in\{1,2,3, \ldots, 1000\})$, die durch 121 teilbar sind. -/
theorem number_theory_605979 :
    Set.ncard {n : ℤ | ∃ x y, n = x^2 + y^2 ∧ 1 ≤ x ∧ x ≤ 1000 ∧ 1 ≤ y ∧ y ≤ 1000 ∧ 121 ∣ n} = 3009 := by
  -- We use the lemma 1 to simplify the problem.
  -- We show that the required set is equal to the set of all numbers of the form 121 * (x ^ 2 + y ^ 2) for x, y in {1, 2, ..., 90}.
  -- We write the latter as a Finset so that we can compute its cardinality.
  have H : {n : ℤ | ∃ x y, n = x ^ 2 + y ^ 2 ∧ 1 ≤ x ∧ x ≤ 1000 ∧ 1 ≤ y ∧ y ≤ 1000 ∧ 121 ∣ n} = (((Finset.Icc 1 90) ×ˢ (Finset.Icc 1 90)).image (fun ((x, y) : ℤ × ℤ) => x ^ 2 + y ^ 2)).map ⟨(121 * ·), by intro x y; simp⟩ := by
    ext n
    simp [-Prod.mk_one_one]
    constructor
    . -- Such n can be written as x ^ 2 + y ^ 2
      -- x and y are multiples of 11.
      rintro ⟨x, y, h₁, h₂, h₃, h₄, h₅, z, rfl⟩
      -- So we obtain a and b such that x = 11 * a and y = 11 * b.
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := lemma_1.1 ⟨z, h₁.symm⟩
      -- The rest is obvious.
      use z
      simp
      use a, b
      ring_nf at h₁
      omega
    . -- This direction is trivial.
      rintro ⟨z, ⟨a, b, h⟩, rfl⟩
      use 11 * a, 11 * b
      ring_nf
      omega
  -- Now we rewrite the problem in terms of the Finset.
  rw [H, Set.ncard_coe_Finset, Finset.card_map]
  -- We compute the cardinality of the Finset by `native_decide`.
  native_decide
