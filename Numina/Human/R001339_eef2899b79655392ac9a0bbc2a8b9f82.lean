import Mathlib

open Finset

/- We define an auxiliary sequence of sets of pairs of natural numbers.
S(n) := The pairs of (a, b) such that 0 < a ∣ b ≤ n.
We will use the `count it twice` technique to count the number of elements of S(n). -/
def S (n : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun (a, b) => a ∣ b)

/- We first show that S(n) = ∑_{i=1}^{n} ⌊n/i⌋. -/
lemma lemma_1 (n : ℕ) :
    #(S n) = ∑ i ∈ Icc 1 n, n / i := by
  -- We cut S(n) into fibers, indexed by the first coordinate.
  let f : ℕ × ℕ → ℕ := fun (a, b) => a
  -- The index of the fiber is ∈ [1, n].
  have hf : ∀ p ∈ S n, f p ∈ Icc 1 n := by
    -- Logically trivial.
    rintro ⟨a, b⟩
    simp only [S, mem_filter, mem_product, mem_Icc, and_imp, f]
    intro a_1 a_2 a_3 a_4 a_5
    simp_all only [and_self, f]
  -- We now count the number of elements in each fiber.
  have H₁ := Finset.card_eq_sum_card_fiberwise hf
  convert H₁ with x hx
  -- We count the number of elements in the fiber indexed by x to be the number of multiples of x in [1, n].
  have H₂ : filter (fun a => f a = x) (S n) = ((Icc 1 n).filter (fun b => x ∣ b)).map ⟨fun b => (x, b), Prod.mk.inj_left x⟩ := by
    -- Logically trivial.
    ext ⟨a, b⟩
    simp only [S, mem_filter, mem_product, mem_Icc, mem_map, Function.Embedding.coeFn_mk,
      Prod.mk.injEq, exists_eq_right_right, f]
    simp_all only [mem_Icc, Prod.forall, f]
    obtain ⟨left, right⟩ := hx
    apply Iff.intro
    · intro a_1
      simp_all only [and_self, true_and, and_true, f]
      obtain ⟨left_1, right_1⟩ := a_1
      obtain ⟨left_1, right_2⟩ := left_1
      obtain ⟨left_1, right_3⟩ := left_1
      obtain ⟨left_1, right_4⟩ := left_1
      obtain ⟨left_2, right_3⟩ := right_3
      subst right_1
      simp_all only [f]
    · intro a_1
      simp_all only [and_self, true_and, and_true, f]
      obtain ⟨left_1, right_1⟩ := a_1
      obtain ⟨left_1, right_2⟩ := left_1
      obtain ⟨left_1, right_3⟩ := left_1
      subst right_1
      simp_all only [f]
  rw [H₂, card_map]
  have hx' : 0 < x := (Finset.mem_Icc.mp hx).1
  -- We now show that the number of multiples of x in [1, n] is ⌊n/x⌋ by giving a bijection that multiplies by x.
  have H₃ : filter (fun b => x ∣ b) (Icc 1 n) = (Icc 1 (n / x)).map ⟨fun b => x * b, mul_right_injective₀ hx'.ne'⟩ := by
    ext y
    simp only [mem_filter, mem_Icc, mem_map, Function.Embedding.coeFn_mk, f]
    constructor
    -- Trivial facts about division.
    . rintro ⟨⟨h₁, h₂⟩, z, rfl⟩
      refine ⟨z, ⟨?_, ?_⟩, rfl⟩
      . nlinarith only [hx', h₁]
      . refine (Nat.le_div_iff_mul_le hx').mpr ?_
        rwa [mul_comm]
    . rintro ⟨z, ⟨h₁, h₂⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, by simp⟩
      . nlinarith only [hx', h₁]
      . rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hx').mp h₂
  simp [H₃]

/- We now show that S(n) = ∑_{i=1}^{n} d(i), where d(i) is the number of divisors of i. -/
lemma lemma_2 (n : ℕ) :
    #(S n) = ∑ i ∈ Icc 1 n, i.divisors.card := by
  -- We cut S(n) into fibers, indexed by the second coordinate.
  let f : ℕ × ℕ → ℕ := fun (a, b) => b
  -- The index of the fiber is ∈ [1, n].
  have hf : ∀ p ∈ S n, f p ∈ Icc 1 n := by
    rintro ⟨a, b⟩
    simp only [S, mem_filter, mem_product, mem_Icc, and_imp, f]
    intro a_1 a_2 a_3 a_4 a_5
    simp_all only [and_self, f]
  -- We now count the number of elements in each fiber.
  have H₁ := Finset.card_eq_sum_card_fiberwise hf
  convert H₁ with x hx
  -- We count the number of elements in the fiber indexed by x to be the number of divisors of x.
  have H₂ : filter (fun a => f a = x) (S n) = ((Icc 1 n).filter (fun a => a ∣ x)).map ⟨fun a => (a, x), Prod.mk.inj_right x⟩ := by
    ext ⟨a, b⟩
    simp only [S, mem_filter, mem_product, mem_Icc, mem_map, Function.Embedding.coeFn_mk,
      Prod.mk.injEq, f]
    simp_all only [mem_Icc, Prod.forall, f]
    obtain ⟨left, right⟩ := hx
    apply Iff.intro
    · intro a_1
      simp_all only [and_true, exists_eq_right, and_self, true_and, f]
      obtain ⟨left_1, right_1⟩ := a_1
      obtain ⟨left_1, right_2⟩ := left_1
      obtain ⟨left_1, right_3⟩ := left_1
      obtain ⟨left_1, right_4⟩ := left_1
      obtain ⟨left_2, right_3⟩ := right_3
      subst right_1
      simp_all only [f]
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left_1, right_1⟩ := h
      obtain ⟨left_1, right_2⟩ := left_1
      obtain ⟨left_2, right_1⟩ := right_1
      obtain ⟨left_1, right_3⟩ := left_1
      subst left_2 right_1
      simp_all only [and_self, f]
  rw [H₂, card_map]
  have hx' : 0 < x := (Finset.mem_Icc.mp hx).1
  congr
  -- We need to show `x.divisors = filter (fun a => a ∣ x) (Icc 1 n)`.
  ext y
  simp only [Nat.mem_divisors, ne_eq, hx'.ne', not_false_eq_true, and_true, mem_filter, mem_Icc,
    iff_and_self, f]
  intro hy
  constructor
  . exact Nat.pos_of_dvd_of_pos hy hx'
  . refine le_trans ?_ (Finset.mem_Icc.mp hx).2
    exact Nat.le_of_dvd hx' hy

/- We now apply lemma_1 and lemma_2 to get a new expression for f(n).
f(n) := (∑_{i=1}^{n} ⌊(n : ℝ) / i⌋) / n = (∑_{i=1}^{n} d(i)) / n. -/
lemma lemma_3 (f : ℕ → ℝ) (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) (n : ℕ) :
    f n = (∑ i ∈ Icc 1 n, i.divisors.card) / n := by
  -- We need to deal with ⌊n / i⌋, and show that it is equal to n / i as nat-division.
  rw [hf]
  congr
  rw [← lemma_2, lemma_1]
  simp only [Nat.cast_sum]
  congr
  ext i
  rw [← Nat.floor_div_eq_div (α := ℝ)]
  refine (Int.natCast_floor_eq_floor ?_).symm
  positivity

/- We now show that n * (n + 1) * (f (n + 1) - f n) = n * d(n+1) - ∑_{i=1}^{n} d(i). -/
lemma lemma_4 (f : ℕ → ℝ) (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) (n : ℕ) (hn : 0 < n) :
    n * (n + 1) * (f (n + 1) - f n) = n * (n + 1).divisors.card - ∑ i ∈ Icc 1 n, i.divisors.card := by
  -- It is a ring identity after cancelling the denominator.
  field_simp [lemma_3 f hf, Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by simp)]
  ring

/- So f(n) < f(n+1) iff ∑_{i=1}^{n} d(i) < n * d(n+1). -/
lemma lemma_5 (f : ℕ → ℝ) (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) (n : ℕ) (hn : 0 < n) :
    f n < f (n + 1) ↔ ∑ i ∈ Icc 1 n, i.divisors.card < n * (n + 1).divisors.card := by
  calc f n < f (n + 1)
    _ ↔ 0 < f (n + 1) - f n := sub_pos.symm
    _ ↔ 0 < n * (n + 1) * (f (n + 1) - f n) := (mul_pos_iff_of_pos_left (by positivity)).symm
    _ ↔ (0 : ℝ) < n * (n + 1).divisors.card - ∑ i ∈ Icc 1 n, i.divisors.card := by rw [lemma_4 f hf n hn]
    _ ↔ ∑ i ∈ Icc 1 n, i.divisors.card < (n * (n + 1).divisors.card : ℝ) := sub_pos
    _ ↔ ∑ i ∈ Icc 1 n, i.divisors.card < n * (n + 1).divisors.card := by norm_cast

/- So f(n+1) < f(n) iff ∑_{i=1}^{n} d(i) > n * d(n+1). -/
lemma lemma_6 (f : ℕ → ℝ) (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) (n : ℕ) (hn : 0 < n) :
    f (n + 1) < f n ↔ n * (n + 1).divisors.card < ∑ i ∈ Icc 1 n, i.divisors.card := by
  calc f (n + 1) < f n
    _ ↔ f (n + 1) - f n < 0 := sub_neg.symm
    _ ↔ n * (n + 1) * (f (n + 1) - f n) < 0 := by
      have h : 0 < (n * (n + 1) : ℝ) := by positivity
      constructor
      . exact mul_neg_of_pos_of_neg h
      . exact fun h' => (pos_iff_neg_of_mul_neg h').mp h
    _ ↔ n * (n + 1).divisors.card - ∑ i ∈ Icc 1 n, i.divisors.card < (0 : ℝ) := by rw [lemma_4 f hf n hn]
    _ ↔ (n * (n + 1).divisors.card : ℝ) < ∑ i ∈ Icc 1 n, i.divisors.card := sub_neg
    _ ↔ n * (n + 1).divisors.card < ∑ i ∈ Icc 1 n, i.divisors.card := by norm_cast

/- We show that ∑_{i=1}^{n} d(i) > n * 2 for n ≥ 6. -/
lemma lemma_7 (n : ℕ) (hn : 6 ≤ n) :
    n * 2 < ∑ i ∈ Icc 1 n, i.divisors.card := by
  -- We use induction on n.
  induction n, hn using Nat.le_induction with
  | base => decide -- We calculate the base case.
  | succ n hn ih =>
    -- We use the inductive hypothesis on n.
    rw [sum_Icc_succ_top (by simp)]
    -- It suffices to show that 1 < d(n+1).
    suffices 1 < (n + 1).divisors.card by omega
    -- Since n+1 has at least 1 and n+1 as its divisors, we are done.
    refine one_lt_card_iff.mpr ?_
    exact ⟨1, n + 1, by simp, by simp, by omega⟩

/- So if n+1 is prime, then f(n+1) < f(n). -/
lemma lemma_8 (f : ℕ → ℝ) (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) (n : ℕ) (hn : 6 ≤ n) (hprime : (n + 1).Prime) :
    f (n + 1) < f n := by
  -- We apply the previous lemma and the fact that a prime number has exactly 2 divisors.
  rw [lemma_6 f hf n (by omega), Nat.Prime.divisors hprime, Finset.card_pair (by omega)]
  exact lemma_7 n hn

/- Let's move to the other direction. We first show that d(n) is not bounded above. -/
lemma lemma_9 : ¬BddAbove {#(Nat.divisors n) | n} := by
  -- We simplify the definition of boundedness.
  simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_setOf_eq, forall_exists_index,
    forall_apply_eq_imp_iff, not_exists, not_forall, not_le]
  -- We now need to show that for any N, there exists n ≥ N such that d(n) > N.
  intro N
  -- For simplicity, we use (N + 1)!.
  use (N + 1).factorial
  -- Any number in the range [1, N+1] divides (N+1)!.
  have H : Finset.Icc 1 (N + 1) ⊆ (N + 1).factorial.divisors := by
    intro x hx
    simp only [Nat.mem_divisors, ne_eq, Nat.factorial_ne_zero, not_false_eq_true, and_true]
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp hx
    exact Nat.dvd_factorial hx₁ hx₂
  -- So we have N < d((N+1)!).
  calc N
    _ < N + 1 := by simp
    _ = (Finset.Icc 1 (N + 1)).card := by simp
    _ ≤ (N + 1).factorial.divisors.card := card_le_card H

/- We now show that for any N, there exists n ≥ N such that d(k) < d(n) for all k < n. In other words, the sequence d(n) keeps achieving new records, there are infinite terms that are larger than any term before it. -/
lemma lemma_10 (N : ℕ) :
    ∃ n ≥ N, ∀ k < n, k.divisors.card < n.divisors.card := by
  -- We use proof by contradiction. Suppose the contrary.
  by_contra! H
  -- Then any term after N is bounded above by some term before N.
  replace H n (hn : n ≥ N) : ∃ k < N, n.divisors.card ≤ k.divisors.card := by
    -- We use strong induction on n.
    induction n using Nat.strongRec with
    | ind n ih =>
      -- We assume the induction hypothesis for all k < n.
      obtain ⟨k, hk₁, hk₂⟩ := H n hn
      -- We now consider whether k < N or k ≥ N.
      by_cases h : k < N
      . -- If k < N, then k is a valid witness.
        exact ⟨k, h, hk₂⟩
      . -- If k ≥ N, then we can use the induction hypothesis on k.
        obtain ⟨k', hk', hk''⟩ := ih k hk₁ (not_lt.mp h)
        refine ⟨k', hk', hk₂.trans hk''⟩
  -- We now show that any term is bounded above by some term before N.
  replace H (n : ℕ) : ∃ k < N, n.divisors.card ≤ k.divisors.card := by
    -- Consider whether n < N or n ≥ N.
    by_cases h : n < N
    . -- If n < N, then n witnesses itself.
      exact ⟨n, h, le_rfl⟩
    . -- If n ≥ N, then we can use the previous conclusion.
      exact H n (not_lt.mp h)
  -- In this way, we can show that d(n) is bounded above.
  have H₁ : BddAbove {#(Nat.divisors n) | n} := by
    -- Since there are only finitely many terms before N, we can take an upper bound M.
    obtain ⟨M, hM⟩ := Finset.bddAbove ((range N).image (fun n => n.divisors.card))
    -- M is also un upper bound for d(n) since any term after N is bounded above by some term before N.
    use M
    rintro - ⟨n, rfl⟩
    simp only [upperBounds, coe_image, coe_range, Set.mem_image, Set.mem_Iio, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq] at hM
    obtain ⟨k, hk₁, hk₂⟩ := H n
    exact hk₂.trans (hM k hk₁)
  -- It contradicts the fact that d(n) is not bounded above.
  exact lemma_9 H₁

theorem number_theory_23606 (f : ℕ → ℝ)
    (hf : ∀ n, f n = (∑ i ∈ Icc 1 n, ⌊(n : ℝ) / i⌋) / n) :
    (∀ N > 0, ∃ n ≥ N, f n < f (n + 1)) ∧ (∀ N > 0, ∃ n ≥ N, f (n + 1) < f n) := by
  constructor <;> intro N hN
  . -- To prove the first direction, we use lemma 10.
    rcases lemma_10 (N + 1) with ⟨n, hn₁, hn₂⟩
    -- We now show that f(n-1) < f(n).
    use n - 1, by omega
    -- We apply lemma 5.
    rw [lemma_5 f hf (n - 1) (by omega)]
    simp only [Nat.one_le_of_lt hn₁, Nat.sub_add_cancel]
    -- Since f(k) < f(n) for all k < n, we have ∑_{i=1}^{n-1} d(i) < (n-1) * d(n).
    calc _
      _ < ∑ i ∈ Icc 1 (n - 1), n.divisors.card := by
        apply sum_lt_sum_of_nonempty
        . exact ⟨1, by simp only [mem_Icc, le_refl, true_and]; omega⟩
        . intro i hi
          simp only [mem_Icc] at hi
          exact hn₂ i (by omega)
      _ = (n - 1) * n.divisors.card := by simp
  . -- To prove the second direction, we use lemma 8.
    -- First, WLOG, we may assume N ≥ 6.
    wlog hN' : 6 ≤ N generalizing N with H
    {
      obtain ⟨n, hn₁, hn₂⟩ := H 6 (by simp) (by simp)
      exact ⟨n, (not_le.mp hN').le.trans hn₁, hn₂⟩
    }
    -- There are infinite primes.
    obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes (N + 1)
    -- We use lemma 8 to show that f(p-1) < f(p).
    use p - 1, by omega
    exact lemma_8 f hf (p - 1) (by omega) (by simp [Nat.one_le_of_lt hp₁, hp₂])
