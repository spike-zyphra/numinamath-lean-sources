import Mathlib

/- We define d(p, m, x, y) as the number of times p divides a - b we can deduce from the fact that a ≡ x and b ≡ y mod p ^ m, where x and y are elements of ℤ/(p ^ m).
It is defined to be m if x = y, and the number of times p divides x - y (as an integer) if x ≠ y. -/
def d (p : ℕ) (m : ℕ) (x y : ZMod (p ^ m)) : ℕ :=
    if x = y then m else padicValInt p (x.cast - y.cast)

/- Lemma 1: p ^ d(p, m, x, y) divides x - y as desired. -/
lemma lemma_1 (p : ℕ) (m : ℕ) (hp : p.Prime) (x y : ℤ) :
    (p ^ d p m x y : ℤ) ∣ x - y := by
  simp only [d, pow_ite]
  split_ifs with h
  . -- If x = y, then d(p, m, x, y) = m, and p ^ m divides x - y.
    simp only [ZMod.intCast_eq_intCast_iff, Nat.cast_pow] at h
    exact Int.ModEq.dvd h.symm
  . -- If x ≠ y, then d(p, m, x, y) is the number of times p divides x - y.
    have inst : Fact p.Prime := ⟨hp⟩
    -- We can write x and y as x.cast + k₁ p^m and y.cast + k₂ p^m for some k₁, k₂ ∈ ℤ.
    obtain ⟨k₁, h₁⟩ := (ZMod.intCast_eq_iff (p ^ m) x x).mp rfl
    obtain ⟨k₂, h₂⟩ := (ZMod.intCast_eq_iff (p ^ m) y y).mp rfl
    simp only [ZMod.natCast_val, Nat.cast_pow] at h₁ h₂
    -- We can then write x - y as (x.cast - y.cast) + (p ^ m) * (k₁ - k₂).
    have h₃ : x - y = (x : ZMod (p ^ m)).cast - (y : ZMod (p ^ m)).cast + (p ^ m) * (k₁ - k₂) := by linear_combination h₁ - h₂
    -- Since x ≠ y in ℤ/(p ^ m), we know that padicValInt p (x.cast - y.cast) < m.
    have H : padicValInt p ((x : ZMod (p ^ m)).cast - (y : ZMod (p ^ m)).cast) < m := by
      have H₁ := padicValInt_dvd (p := p) ((x : ZMod (p ^ m)).cast - (y : ZMod (p ^ m)).cast)
      -- We have ¬p ^ m ∣ x.cast - y.cast.
      have H₂ : ¬(p ^ m : ℤ) ∣ (x : ZMod (p ^ m)).cast - (y : ZMod (p ^ m)).cast := by
        -- We have ¬p ^ m ∣ x - y from x ≠ y in ℤ/(p ^ m).
        rw [ZMod.intCast_eq_intCast_iff, Int.modEq_comm, Int.modEq_iff_dvd] at h
        contrapose! h
        simp only [Nat.cast_pow, h₃]
        exact (dvd_add_right h).mpr (dvd_mul_right _ _)
      -- If m ≤ padicValInt p (x.cast - y.cast), then p ^ m ∣ x.cast - y.cast, contradicting H₂.
      contrapose! H₂
      exact (pow_dvd_pow (p : ℤ) H₂).trans H₁
    -- Now the proposition is clear.
    rw [h₃]
    exact dvd_add (padicValInt_dvd _) (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) H.le) _)

/- We define f(p, m, a) as the number of times p divides the product of all differences of possible couples of elements of a knowing a_i mod p^m for all i.
It is defined to be the sum of d(p, m, a_i, a_j) for all i < j. -/
def f (p : ℕ) (m : ℕ) (a : Fin 6 → ZMod (p ^ m)) : ℕ :=
    ∑ i, ∑ j, if i < j then d p m (a j) (a i) else 0

/- Lemma 2: p ^ f(p, m, a) divides the product of all differences of possible couples of elements of a knowing a_i mod p^m for all i. -/
lemma lemma_2 (p : ℕ) (m : ℕ) (hp : Nat.Prime p) (a : Fin 6 → ℤ) :
    (p ^ f p m (fun i => a i) : ℤ) ∣ ∏ i, ∏ j, if i < j then (a j - a i) else 1 := by
  -- Rewrite the sum in the exponent as a product.
  simp only [f, ← Finset.prod_pow_eq_pow_sum, pow_ite, pow_zero]
  -- Since we have the divisibility of each term, we can use the product of products of divisibility.
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => ?_))
  split_ifs with h
  . exact lemma_1 p m hp (a j) (a i)
  . simp

/- Lemma 3: If k ≤ f(p, m, a) for all possible combinations of a_i mod p^m for all i, then p^k divides the product of all differences of possible couples of elements of a for all possible integers a_i. -/
lemma lemma_3 (p : ℕ) (m : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (∀ a : Fin 6 → ZMod (p ^ m), k ≤ f p m a) →
    ∀ a : Fin 6 → ℤ, (p ^ k : ℤ) ∣ ∏ i, ∏ j, if i < j then (a j - a i) else 1 := by
  -- It is a direct consequence of Lemma 2.
  intro H a
  specialize H (fun i => a i)
  apply pow_dvd_pow p at H
  zify at H
  exact H.trans (lemma_2 p m hp a)

/- Alban

a) Show that the product of all differences of possible couples of six given positive integers is divisible by 960 (original from Albania).

b) Show that the product of all differences of possible couples of six given positive integers. is divisible by 34560 (modified by problem selecting committee). -/
/- ALB

a) Show that the product of all differences of possible couples of six given positive integers is divisible by 960 (original from Albania).

b) Show that the product of all differences of possible couples of six given positive integers. is divisible by 34560 (modified by problem selecting committee). -/
theorem number_theory_604837 (a : Fin 6 → ℤ) (ha : ∀ i, a i > 0) :
    (960 ∣ ∏ i, ∏ j, if i < j then (a j - a i) else 1) ∧ (34560 ∣ ∏ i, ∏ j, if i < j then (a j - a i) else 1) := by
  -- Positivity is redundant, so we can clear it.
  clear ha
  -- Since 960 ∣ 34560, we only prove the stronger statement.
  suffices H : 34560 ∣ ∏ i, ∏ j, if i < j then (a j - a i) else 1
  from lcm_dvd_iff.mp H
  -- We can rewrite 34560 as the least common multiple of 2^8, 3^5, and 5.
  rw [show (34560 : ℤ) = Multiset.lcm {256, 27, 5} by decide,
      Multiset.lcm_dvd]
  simp
  -- We can now apply Lemma 3 to each of the three factors.
  refine ⟨?_, ?_, ?_⟩
  . -- We check each case modulo 4.
    apply lemma_3 2 2 (by norm_num) 8
    native_decide
  . -- We check each case modulo 3.
    apply lemma_3 3 1 (by norm_num) 3
    native_decide
  . -- We check each case modulo 5.
    apply lemma_3 5 1 (by norm_num) 1
    native_decide
