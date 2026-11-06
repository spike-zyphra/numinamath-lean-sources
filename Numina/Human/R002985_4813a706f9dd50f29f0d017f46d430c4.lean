import Mathlib

-- Define F(n) = 2^(2^n) + 1.
def F (n : ℕ) := 2^(2^n) + 1

-- Show that 3 ≤ F(n) for all n.
lemma lemma_1 n : 3 ≤ F n := by
  simp [F]
  nth_rw 1[← pow_one 2]
  exact pow_le_pow (le_refl _) one_le_two (Nat.one_le_pow _ _ zero_lt_two)

-- Show that F(a) ≤ F(b) for all a ≤ b.
lemma lemma_2 {a b : ℕ} (hab : a ≤ b) : F a ≤ F b := by
  simp [F]
  apply pow_le_pow (le_refl _) one_le_two
  apply pow_le_pow_right₀ one_le_two hab

-- Show that F(n + 1) - 2 = F(n) * (F(n) - 2) for all n.
lemma lemma_3 n : F (n + 1) - 2 = F n * (F n - 2) := by
  zify [show ∀ n, 2 ≤ F n by intro n; linarith [lemma_1 n]]
  simp [F]
  ring

-- Show that F(b) - 2 = (F a - 2) * ∏ i ∈ [a, b), F i for all a < b.
lemma lemma_4 {a b : ℕ} (hab : a < b) : F b - 2 = (F a - 2) * ∏ i ∈ Finset.Ico a b, F i := by
  rw [show b = a + (b - a) by omega]
  have hk0 : b - a ≠ 0 := by omega
  generalize b - a = k at hk0 ⊢
  clear hab b
  -- It is enough to show that F(a + k) - 2 = (F a - 2) * (F a - 2) * ∏ i ∈ [a, a + k), F i
  -- for all k ≠ 0.
  -- Proof by induction.
  induction k with
  | zero => contradiction
  | succ k ih =>
    -- Consider k + 1.
    cases k with
    -- If k = 0 then F(a + 1) - 2 = (F(a) - 2) * F(a) follows from lemma_3.
    | zero => simp [lemma_3, mul_comm]
    | succ k' =>
      -- If k = k' + 1 then lemma_3 implies
      -- F(a + (k' + 1 + 1)) - 2 = F(a + (k + 1)) * (F(a + (k + 1)) - 2).
      rw [show a + (k' + 1 + 1) = (a + (k' + 1)) + 1 by ring, lemma_3]
      -- Use the induction hypothesis to rewrite F(a + (k + 1)) - 2.
      rw [ih (by omega), Finset.prod_Ico_succ_top (by linarith)]
      ring

-- Show that a ≠ b implies that (F a).minFac ≠ (F b).minFac.
lemma lemma_5 {a b : ℕ} (hab : a ≠ b) : (F a).minFac ≠ (F b).minFac := by
  -- Without loss of generality, assume that a < b.
  wlog h : a < b
  · simp at h
    apply Ne.symm
    apply this hab.symm
    rw [lt_iff_le_and_ne]
    exact ⟨h, hab.symm⟩
  -- Assume that (F a).minFac = (F b).minFac and derive a contradiction.
  by_contra! h_eq
  -- We have (F a).minFac = (F b).minFac divides F b.
  have hdvd1 : (F a).minFac ∣ F b := by
    rw [h_eq]
    exact Nat.minFac_dvd _
  -- Show that (F a).minFac divides F b - 2.
  have hdvd2 : (F a).minFac ∣ F b - 2 := by
    -- lemma_4 implies that
    -- F b - 2 = (F a - 2) * ∏ i ∈ [a, b), F i = (F a - 2) * F a * ∏ i ∈ (a, b), F i.
    rw [lemma_4 h]
    rw [Finset.prod_eq_prod_Ico_succ_bot h]
    -- (F a).minFac divides F a so F a = (F a).minFac * k for some k.
    have ⟨k, hk⟩ := Nat.minFac_dvd (F a)
    nth_rw 3 [hk]
    -- It is now easy to show that (F a).minFac divides
    -- (F a - 2) * F a * ∏ i ∈ (a, b), F i = (F a).minFac * (k * (F a - 2) * ∏ i ∈ (a, b), F i).
    rw [show ∀ x y z : ℕ, x * (y * z) = y * (x * z) by intros; ring]
    simp_rw [mul_assoc]
    apply Nat.dvd_mul_right
  have ha := lemma_1 a
  -- Show that (F a).minFac = 2.
  have heq2 : (F a).minFac = 2 := by
    -- (F a).minFac and 2 are prime numbers, so it is enough to show that
    -- (F a).minFac divides 2.
    rw [← Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime (by linarith)) Nat.prime_two]
    have hb := lemma_1 b
    -- We have 2 = F b - (F b - 2) and (F a).minFac divides both F b and F b - 2,
    -- so (F a).minFac divides 2.
    rw [show 2 = F b - (F b - 2) by omega]
    apply Nat.dvd_sub (by omega) hdvd1 hdvd2
  -- We get that F a is even (because 2 = (F a).minFac ∣ F a).
  have heven : Even (F a) := by
    rw [even_iff_two_dvd]
    rw [← heq2]
    apply Nat.minFac_dvd
  -- Show that F a is odd.
  contrapose! heven
  -- F a = 2^2^a + 1 and 2^2^a is even, so F a is odd.
  simp only [Nat.not_even_iff_odd, F]
  apply Even.add_odd _ odd_one
  rw [Nat.even_pow' (by positivity)]
  exact even_two

/- Let $n$ be a natural number and $F_{n}=2^{2^{n}}+1$. Show that there exist at least $n+1$ prime numbers less than or equal to $F_{n}$.

## Solutions -/
theorem number_theory_139093 (n : ℕ) :
    {p | p.Prime ∧ p ≤ F n}.encard ≥ n + 1 := calc
  -- Show that (fun i => (F i).minFac) '' Set.Icc 0 n is a subset of {p | p.Prime ∧ p ≤ F n}.
  _ ≥ ((fun i => (F i).minFac) '' Set.Icc 0 n).encard := by
    apply Set.encard_le_card
    intro x
    simp only [Set.mem_image, Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq, forall_exists_index,
      and_imp]
    intro i hi hx
    -- It is enough to show that (F i).minFac is prime and (F i).minFac ≤ F n for i ≤ n.
    subst x
    constructor
    -- (F i).minFac is prime because F i ≠ 0.
    · apply Nat.minFac_prime
      linarith [lemma_1 i]
    -- We have (F i).minFac ≤ F i ≤ F n (by lemma_2).
    · trans F i
      · apply Nat.minFac_le
        linarith [lemma_1 i]
      · exact lemma_2 hi
  -- Show that the cardinality of (fun i => (F i).minFac) '' Set.Icc 0 n is n + 1.
  _ = n + 1 := by
    -- The cardinality of Set.Icc 0 n is n + 1, so it is enough to show that
    -- (fun i => (F i).minFac) is injective.
    rw [Function.Injective.encard_image]
    · rw [Set.Finite.encard_eq_coe_toFinset_card]
      simp
      simp [Set.finite_Icc]
    intro a b
    simp
    intro eq
    -- The injectivity of (F i).minFac follows from lemma_5.
    contrapose! eq
    apply lemma_5 eq