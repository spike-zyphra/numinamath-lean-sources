import Mathlib

open Finset

/-For any positive integer $n$, let $\tau(n)$ denote the number of positive divisors of $n$. If $n$ is a positive integer such that $\frac{\tau\left(n^{2}\right)}{\tau(n)}=3$, compute $\frac{\tau\left(n^{7}\right)}{\tau(n)}$.-/
theorem number_theory_610439 (n : ℕ) (npos : 0 < n) (hn : ((n ^ 2).divisors.card : ℚ) / n.divisors.card = 3) :
((n ^ 7).divisors.card : ℚ) / n.divisors.card = 29 := by
-- Simplify the assumption hn using `Nat.card_divisors`
  rw [Nat.card_divisors, Nat.card_divisors, Nat.primeFactors_pow] at hn
  simp [Nat.factorization_pow] at hn; rw [← prod_div_distrib] at hn
-- Prove the following auxillary inequality for prime factors of $n$
  have aux : ∀ p ∈ n.primeFactors, 3 / 2 ≤ (2 * n.factorization p + 1 : ℚ) / (n.factorization p + 1) := by
    intro p hp; simp at hp; rcases hp with ⟨ppr, pdvd,_⟩
    have : Fact (p.Prime) := ⟨ppr⟩
    rw [Nat.factorization_def, div_le_div_iff₀, ← sub_nonneg]; ring_nf
    rw [← neg_le_iff_add_nonneg', neg_neg]; norm_cast
    rw [Nat.one_le_iff_ne_zero, ← dvd_iff_padicValNat_ne_zero]; exact pdvd
    any_goals positivity
    exact ppr
-- Prove that $n$ has at most $2$ distinct prime factors by contradiction:
-- if $n$ has at least $3$ prime factors, we show that the product on the LHS of hn is larger than $3$
  have cardnpF : n.primeFactors.card ≤ 2 := by
    by_contra!; rw [Nat.lt_iff_add_one_le] at this; norm_num at this
    obtain ⟨S, ⟨Ssubs, Scard⟩⟩ := exists_subset_card_eq this
    rw [card_eq_three] at Scard; rcases Scard with ⟨p, q, r, ⟨pneq, pner, qner, hS⟩⟩
    let Ssubs' := Ssubs; simp [hS, subset_iff] at Ssubs'
    rcases Ssubs' with ⟨⟨ppr, pdvd,h⟩, ⟨qpr, qdvd,h'⟩, ⟨rpr, rdvd,h''⟩⟩; clear h h' h''
    rw [← union_sdiff_of_subset Ssubs, prod_union] at hn; nth_rw 1 [hS] at hn
    repeat rw [prod_insert] at hn
    convert hn; simp; push_neg; symm; apply ne_of_lt; calc
      _ < (3 : ℚ) / 2 * (3 / 2 * (3 / 2)) * 1 := by norm_num
      _ ≤ _ := by
        apply mul_le_mul; apply mul_le_mul
        · exact aux p (by simp; split_ands; exact ppr; exact pdvd; positivity)
        apply mul_le_mul
        · exact aux q (by simp; split_ands; exact qpr; exact qdvd; positivity)
        exact aux r (by simp; split_ands; exact rpr; exact rdvd; positivity)
        any_goals positivity
        rw [le_div_iff₀, one_mul]; norm_cast; apply prod_le_prod
        any_goals intros; omega
        positivity
    simp; exact qner; simp; exact And.intro pneq pner
    exact disjoint_sdiff
-- So we have two cases : $n$ has one prime factor or $n$ has two prime factors
  interval_cases hcard : n.primeFactors.card
  · simp at hcard; rcases hcard with _|h; omega
    simp [h] at hn
-- If $n$ has one prime factor, we are quickly led to a linear arithmetic contradiction by simplifying hn
  · rw [card_eq_one] at hcard; rcases hcard with ⟨p, hpF⟩
    simp [hpF] at hn; symm at hn
    rw [eq_div_iff, ← sub_eq_zero] at hn; ring_nf at hn
    norm_cast at hn; omega; positivity
-- If $n$ has two prime factors, we first simplify the condiction hn and the final goal
  rw [card_eq_two] at hcard; rcases hcard with ⟨p, q, ⟨pneq, hpF⟩⟩
  let hpF' := hpF; simp [Finset.ext_iff] at hpF'
  have := hpF' p; simp at this; rcases this with ⟨ppr,_,_⟩
  have : Fact (p.Prime) := ⟨ppr⟩
  specialize hpF' q; simp at hpF'; rcases hpF' with ⟨qpr,_,_⟩
  have : Fact (q.Prime) := ⟨qpr⟩
  rw [hpF, prod_insert, prod_singleton] at hn; field_simp at hn
  rw [← sub_eq_zero] at hn; ring_nf at hn
  have : (-2:ℚ) - n.factorization p + ((n.factorization p) * (n.factorization q) - (n.factorization q)) =
  (n.factorization p - 1) * (n.factorization q - 1) - 3 := by ring
  rw [this, sub_eq_zero, show (1:ℚ) = (1:ℕ) by rfl, ← Nat.cast_sub, ← Nat.cast_sub] at hn
  norm_cast at hn; rw [Nat.card_divisors, Nat.card_divisors, Nat.primeFactors_pow]
  rw [hpF]; repeat rw [prod_insert, prod_singleton]
  simp [Nat.factorization_pow]
-- Prove that $(n.factorization p, n.factorization q)$ is $(2, 4)$ or $(4,2)$, then finish the goal by plugging in these values
  by_cases hp : n.factorization p - 1 = 1
  · simp [hp] at hn; simp at hp
    simp [hp, hn]; norm_num
  have : (n.factorization p - 1) ∣ 3 := by use (n.factorization q - 1); rw [← hn]
  rw [Nat.Prime.dvd_iff_eq Nat.prime_three (by omega)] at this
  rw [← this] at hn; replace hn : n.factorization q - 1 = 1 := by omega
  symm at this; simp at this hn; norm_num [this, hn]
-- Finish the rest trivial goals
  any_goals exact not_mem_singleton.mpr pneq
  any_goals positivity
  all_goals rw [Nat.factorization_def, Nat.one_le_iff_ne_zero, ← dvd_iff_padicValNat_ne_zero]
  all_goals assumption