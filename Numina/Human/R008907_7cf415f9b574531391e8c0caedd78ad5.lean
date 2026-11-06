import Mathlib

/-A book with 53 pages numbered 1 to 53 has its pages renumbered in reverse, from 53 to 1. For how many pages do the new page number and old page number share the same units digit?-/
theorem algebra_13702 :
    {n | n ∈ Finset.Icc 1 53 ∧ (54 - n) % 10 = n % 10}.ncard = 11 := by
  -- Each page is assigned two numbers. We can generalize the numbers assigned to page $x$ to be the pair $x$ and $54-x$ for $1 \leq x \leq 53$. That is, if $x = 1$, then we can see that page number one is assigned the numbers $1$ and $54-1 = 53$.
  have :∃s, s = {n | n ∈ Finset.Icc 1 53 ∧ (54 - n) % 10 = n % 10} := by simp
  rcases this with ⟨s, hs⟩
  rw [hs.symm]
  simp at hs
  -- Possibilities for $x$ are: 2, 7, 12, 17, 22, 27, 32, 37, 42, 47, and 52. Therefore, there are $\boxed{11}$ such pages.
  have : s = {2, 7, 12, 17, 22, 27, 32, 37, 42, 47, 52} := by
    rw [hs]
    ext n
    simp
    constructor
    . rintro ⟨⟨hx₁, hx₂⟩, hx₃⟩
      rw [←Nat.ModEq] at hx₃
      -- It is fairly easy to see that the units digits of $x$ and $54-x$ will only be the same if $x$ has a units digit of $2$ or a units digit of $7$. Thus, we simply must count how many such $x$ there are between $1$ and $54$.
      have _n_lt_54 : n < 54 := by linarith
      have _54_sub_n_int := Int.ofNat_sub _n_lt_54.le
      have : n ≡ 2 [MOD 10] ∨ n ≡ 7 [MOD 10] := by
        repeat rw [Nat.ModEq]
        rw [Nat.ModEq] at hx₃
        omega
      rcases this with (eq2 | eq7)
      . -- n ≡ 2 [MOD 10]
        have : ∀n < 54, n % 10 = 2 → n = 2 ∨ n = 12 ∨ n = 22 ∨ n = 32 ∨ n = 42 ∨ n = 52 := by
          -- exhaustion, but human can do
          decide
        rw [Nat.ModEq] at eq2
        simp at eq2
        specialize this n (by linarith) eq2
        repeat rcases this with (r | this); rw [r]; simp
        rw [this]; simp
      . have : ∀n < 54, n % 10 = 7 → n = 7 ∨ n = 17 ∨ n = 27 ∨ n = 37 ∨ n = 47 := by
          -- exhaustion, but human can do
          decide
        rw [Nat.ModEq] at eq7
        simp at eq7
        specialize this n (by linarith) eq7
        repeat rcases this with (r | this); rw [r]; simp
        rw [this]; simp
    . intro hx
      repeat rcases hx with (r | hx); rw [r]; simp
      rw [hx]; simp

  rw [this]
  repeat rw [Set.insert_eq, Set.ncard_union_eq, Set.ncard_singleton]
  rw [Set.ncard_singleton]
  repeat simp
