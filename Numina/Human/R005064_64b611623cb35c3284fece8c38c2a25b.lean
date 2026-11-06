import Mathlib

/- Find all functions $f$ defined on the natural numbers that take values among the natural numbers for which

$$
(f(n))^{p} \equiv n \quad \bmod f(p)
$$

for all $n \in \mathbf{N}$ and all prime numbers $p$. -/
theorem number_theory_605351 :
    {f : ℕ → ℕ | ∀ n p, p.Prime → (f n)^p ≡ n [MOD f p]} = {id} ∪ {f : ℕ → ℕ | ∀ p, p.Prime → f p = 1} ∪ {f : ℕ → ℕ | f 2 = 2 ∧ (∀ p, 2 < p → p.Prime → f p = 1) ∧ (∀ n, f n ≡ n [MOD 2])} := by
  ext f
  simp
  constructor
  swap
  -- We first check that the three cases are sufficient.
  {
    rintro ((rfl | H) | ⟨H₁, H₂, H₃⟩)
    . -- If f is the identity function, then f(n) ^ p ≡ n [MOD f(p)] for all n and p by Fermat's little theorem.
      intro n p hp
      have inst : Fact p.Prime := ⟨hp⟩
      simp [← ZMod.natCast_eq_natCast_iff]
    . -- If f p = 1 for all prime p, then f(n) ^ p ≡ n [MOD f(p)] since f(p) = 1.
      intro n p hp
      simp [H p hp, Nat.modEq_one]
    . -- If f 2 = 2, f p = 1 for all prime p > 2 and f n ≡ n [MOD 2] for all n, then f(n) ^ p ≡ n [MOD f(p)] for all n and p.
      intro n p hp
      rcases (Nat.Prime.two_le hp).eq_or_lt with rfl | h
      . -- For p = 2, we have f(n) ^ 2 ≡ f(n) ≡ n [MOD 2].
        rw [H₁]
        calc f n ^ 2
          _ ≡ f n [MOD 2] := by simp [← ZMod.natCast_eq_natCast_iff]
          _ ≡ n [MOD 2] := H₃ n
      . -- For p > 2, f(p) = 1.
        rw [H₂ p h hp]
        exact Nat.modEq_one
  }
  -- Now, we show that the three cases are necessary.
  intro H
  -- First, we show that f(p) = 1 or f(p) = p for all prime p.
  have H₁ (p : ℕ) (hp : p.Prime) : f p = 1 ∨ f p = p := by
    -- Let's plug in p, p into the given equation.
    specialize H p p hp
    -- We get that p ≡ 0 [MOD f(p)].
    replace H : p ≡ 0 [MOD f p] := by
      calc p
        _ ≡ f p ^ p [MOD f p] := H.symm
        _ ≡ 0 [MOD f p] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self (f p) (Nat.Prime.ne_zero hp))
    -- So f(p) must divide p.
    simp [Nat.modEq_zero_iff_dvd] at H
    -- So f(p) = 1 or f(p) = p.
    exact (Nat.dvd_prime hp).mp H
  -- Now, let's discuss whether the set of primes p such that f(p) = p is finite or infinite.
  let S := {p | p.Prime ∧ f p = p}
  rcases S.infinite_or_finite with H₂ | H₂
  {
    -- If the set is infinite, we will show that f(n) = n for all n.
    left; left
    -- If otherwise, there is some n such that f(n) ≠ n.
    by_contra! H₃
    simp [funext_iff] at H₃
    rcases H₃ with ⟨n, hn⟩
    zify at hn
    -- So |f(n) - n| is a positive integer.
    rw [← ne_eq, ← sub_ne_zero, ← Int.natAbs_ne_zero] at hn
    -- Since `S` is infinite, there exists a prime p > |f(n) - n| such that f(p) = p.
    obtain ⟨p, ⟨hp₁, hp₂⟩, hp₃⟩ : ∃ p, p ∈ S ∧ (↑(f n) - ↑n : ℤ).natAbs < p := H₂.exists_gt _
    have inst : Fact p.Prime := ⟨hp₁⟩
    -- Plugging in n, p into the given equation, we get that n ≡ f(n) [MOD p].
    specialize H n p hp₁
    rw [hp₂] at H
    replace H : n ≡ f n [MOD p] := by
      calc n
        _ ≡ f n ^ p [MOD p] := H.symm
        _ ≡ f n [MOD p] := by simp [← ZMod.natCast_eq_natCast_iff]
    -- So p ∣ |f(n) - n|.
    rw [Nat.modEq_iff_dvd, ← Int.natAbs_dvd_natAbs] at H
    simp at H
    -- But |f(n) - n| < p, so we get a contradiction.
    apply Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn) at H
    exact H.not_lt hp₃
  }
  -- Now, let's discuss whether the set of primes p such that f(p) = p is empty or nonempty.
  rcases S.eq_empty_or_nonempty with H₃ | ⟨a, ha⟩
  {
    -- If the set is empty, we clearly have f(p) = 1 for all prime p.
    left; right
    intro p hp
    specialize H₁ p hp
    simp [Set.ext_iff, S] at H₃
    simpa [H₃ p hp] using H₁
  }
  -- If the set is nonempty, we take the maximal element q of the set.
  rcases Set.Finite.exists_le_maximal H₂ ha with ⟨q, -, ⟨hq₁, hq₂⟩, hq₃⟩
  simp [S] at hq₃
  -- We claim that q = 2.
  obtain rfl : q = 2 := by
    -- We will show that for all prime p > q, we have p ≡ 1 [MOD q].
    have H₃ (p : ℕ) (hp₁ : p.Prime) (hp₂ : q < p) : p ≡ 1 [MOD q] := by
      -- Plugging in p, q into the given equation, we get that f(p) ^ q ≡ p [MOD f(q)].
      specialize H p q hq₁
      -- Since f(p) = 1 and f(q) = q, we get that p ≡ 1 [MOD q].
      -- Note that f(p) = 1 because q is maximal in the set, so p is not in the set.
      have hp₃ : f p = 1 := by
        specialize H₁ p hp₁
        contrapose! H₁
        refine ⟨H₁, fun h₁ => ?_⟩
        specialize hq₃ hp₁ h₁ hp₂.le
        exact hq₃.not_lt hp₂
      simp [hq₂, hp₃] at H
      exact H.symm
    have inst : NeZero q := ⟨Nat.Prime.ne_zero hq₁⟩
    -- By Dirichlet's theorem, there exists a prime p > q such that p ≡ -1 [MOD q].
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := Nat.forall_exists_prime_gt_and_eq_mod (show IsUnit (-1 : ZMod q) by simp) q
    -- So 1 ≡ -1 [MOD q].
    specialize H₃ p hp₂ hp₁
    simp [← ZMod.natCast_eq_natCast_iff, hp₃] at H₃
    replace H₃ : (2 : ℕ) = (0 : ZMod q) := by linear_combination -H₃
    -- So q ∣ 2 and thus q = 2.
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at H₃
    exact (Nat.prime_dvd_prime_iff_eq hq₁ Nat.prime_two).mp H₃
  -- We now show that f(2) = 2 and f(p) = 1 for all prime p > 2.
  -- Also, we show that f(n) ≡ n [MOD 2] for all n.
  right
  refine ⟨hq₂, ?_, ?_⟩
  . -- Since q = 2 is maximal in the set, we have f(p) = 1 for all prime p > 2.
    intro p hp₁ hp₂
    specialize H₁ p hp₂
    contrapose! H₁
    refine ⟨H₁, fun h => ?_⟩
    specialize hq₃ hp₂ h hp₁.le
    exact hq₃.not_lt hp₁
  . -- Plugging in n, 2 into the given equation, we get that f(n) ^ 2 ≡ f(n) ≡ n [MOD 2].
    intro n
    specialize H n 2 hq₁
    rw [hq₂] at H
    calc f n
      _ ≡ f n ^ 2 [MOD 2] := by simp [← ZMod.natCast_eq_natCast_iff]
      _ ≡ n [MOD 2] := H
