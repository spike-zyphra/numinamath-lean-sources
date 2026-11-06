import Mathlib
import Aesop

set_option trace.aesop true
open ArithmeticFunction
notation "ℕ⁺" => ℕ+
def τ := σ 0

open Nat Finsupp

/-Let $a_{1}=2$ and, for every positive integer $n$, let $a_{n+1}$ be the smallest integer strictly greater than $a_{n}$ that has more positive divisors than $a_{n}$. Prove that $2 a_{n+1}=3 a_{n}$ only for finitely many indices $n$.-/

-- If p₀ is not in S, removing p₀ from S does not change the product.
lemma lemma1 [ DecidableEq α ] [ CommMonoid β ]
( S : Finset α ) { f : α -> β } ( p₀ : α )
: p₀ ∉ S -> ∏ p ∈ S, f p = ∏ p ∈ S \ {p₀}, f p := by 
  intro hp
  refine Finset.prod_bijective id Function.bijective_id ?_ ?_ <;> dsimp
  simp [show S \ {p₀} = S by {
    nth_rw 2 [← Finset.erase_eq_of_not_mem hp]
    exact Finset.sdiff_singleton_eq_erase p₀ S
  }]
  exact fun i a => rfl

-- If f and g agree on all elements of S, then their products over S are equal.
lemma lemma2 [ DecidableEq α ] [ CommMonoid β ]
( S : Finset α ) ( f g : α -> β ) ( h : ∀ p ∈ S, f p = g p )
: ∏ p ∈ S, f p = ∏ p ∈ S, g p :=
  Finset.prod_congr rfl h
-- If f(i) is positive for all i in S, then the product is positive.
lemma lemma3 ( S : Finset α ) { f : α -> ℕ } : (∀ i ∈ S, 0 < f i) -> 0 < ∏ i ∈ S, f i := by 
  intro hf
  simp
  exact hf

-- If A is subset of B, and for all i, f(i) ≤ g(i), and g(i) ≥ 1,
-- then the product over A of f(i) ≤ product over B of g(i).
lemma lemma4 [ DecidableEq α ] ( A B : Finset α ) { f g : α -> ℕ }
( hab : A ⊆ B )
( hg : ∀ i, 1 ≤ g i )
( h : ∀ i, f i ≤ g i )
: ∏ i ∈ A, f i ≤ ∏ i ∈ B, g i := by 
  rw [← Finset.prod_sdiff hab]
  have h' : ∏ i ∈ A, f i ≤ ∏ i ∈ A, g i := Finset.prod_le_prod' fun i a => h i
  apply h'.trans; clear h hab h' f
  refine Nat.le_mul_of_pos_left (∏ i ∈ A, g i) ?_
  exact lemma3 (B \ A) fun i a => hg i


-- The exponent of prime p in the factorization of p * q equals the exponent in q plus one.
lemma lemma5 ( p q : ℕ ) ( hp : p.Prime ) ( hq : 0 < q ) : (p * q).factorization p = q.factorization p + 1 := by 
  rw [mul_comm, ← Nat.primeFactorsList_count_eq, ← Nat.primeFactorsList_count_eq]
  rw [show 1 = List.count p [p] by simp_all only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_self, List.mem_cons, or_false, List.count_eq_one_of_mem]]
  rw [← Nat.primeFactorsList_prime hp]
  rw [← @List.count_append]
  refine List.Perm.count_eq ?_ p
  refine Nat.perm_primeFactorsList_mul ?_ ?_
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [lt_self_iff_false]
  exact Nat.Prime.ne_zero hp

-- If p and p' are different primes, then the exponent of p' in p * n equals that in n.
lemma lemma6 ( n p p' : ℕ ) ( hp : p.Prime ) ( h : p ≠ p' )
: (p * n).factorization p' = n.factorization p' := by 
  by_cases hn : n = 0
  rw [hn, mul_zero]
  by_cases hp' : p'.Prime
  {
    rw [← Nat.primeFactorsList_count_eq, ← Nat.primeFactorsList_count_eq]
    rw [List.Perm.count_eq (@Nat.perm_primeFactorsList_mul p n hp.ne_zero hn) p']
    rw [@List.count_append, Nat.primeFactorsList_prime hp]
    rw [@Nat.add_eq_right]
    refine List.count_eq_zero.mpr ?_
    refine List.not_mem_cons_of_ne_of_not_mem (_root_.id (Ne.symm h)) ?_
    simp_all only [ne_eq, List.not_mem_nil, not_false_eq_true]
  }
  rw [factorization_eq_zero_of_non_prime (p * n) hp']
  rw [factorization_eq_zero_of_non_prime n hp']

-- Generalization: the exponent of p in p^k * q equals exponent in q plus k.
lemma lemma7 ( k p q : ℕ ) ( hp : p.Prime ) ( hq : 0 < q ) : (p ^ k * q).factorization p = q.factorization p + k := by 
  induction k with
  | zero => simp
  | succ k' ih => {
    rw [Nat.pow_succ', Nat.mul_assoc, lemma5 p _ hp <| by {
      refine Mathlib.Tactic.Ring.mul_exp_pos k' ?_ hq
      exact Prime.pos hp
    }, ih]
    exact rfl
  }

-- Generalization of cancelation for powers of p different from p'.
lemma lemma8 k ( n p p' : ℕ ) ( hp : p.Prime ) ( h : p ≠ p' )
: (p ^ k * n).factorization p' = n.factorization p' := by 
  induction k with
  | zero => simp
  | succ k' ih => {
    rw [Nat.pow_succ', Nat.mul_assoc, lemma6 _ p p' hp h, ih]
  }


-- Removing p from the prime factors of p * n equals removing p from n's prime factors.
lemma lemma9 ( p : ℕ ) ( hp : p.Prime )
: (p * n).primeFactors \ {p} = n.primeFactors \ {p} := by 
  refine Finset.ext_iff.mpr ?_
  simp
  intro e he hp'
  constructor
  intro ⟨h1, h2, h3⟩
  constructor
  rcases @Nat.Prime.dvd_mul e p n hp' |>.mp h1 with h | h
  {
    have H ( p q : ℕ ) ( hp : p.Prime ) ( hq : q.Prime ) ( H : p ≠ q ) : ¬ p ∣ q := by {
      intro nh
      unfold Nat.Prime at hq
      cases' hq with h1 h2
      obtain ⟨r, hr⟩ := nh
      have h := h2 p r hr
      rcases h with h | h
      have h : ¬ IsUnit p := by {
        subst hr
        simp_all only [isUnit_iff_eq_one, one_mul, ne_eq, not_true_eq_false]
        subst h
        have fwd : False := Nat.not_prime_one hp
        clear hp
        simp_all only [not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true]
      }
      contradiction
      rw [@Nat.isUnit_iff] at h
      rw [h, mul_one] at hr
      simp only [hr] at *; clear hr h r h2 h1
      contradiction
    }
    exact H e p hp' hp he h |>.elim
  }
  exact h
  exact h3
  intro ⟨h1, h2⟩
  constructor
  exact Dvd.dvd.mul_left h1 p
  constructor
  exact Nat.Prime.ne_zero hp
  exact h2

-- By induction on k, prove that removing prime p from the prime factors
-- of p^k * n is the same as removing p from the prime factors of n.
lemma lemma10 ( p k : ℕ ) ( hp : p.Prime )
: (p ^ k * n).primeFactors \ {p} = n.primeFactors \ {p} := by 
  induction k with
  | zero => simp
  | succ k' ih => {
    rw [Nat.pow_succ', Nat.mul_assoc, lemma9 p hp, ih]
  }


-- Set difference associativity: removing B then C equals removing B∪C once.
lemma lemma11 ( A B C : Finset ℕ ) : (A \ B) \ C = A \ (B ∪ C) := by 
  refine Finset.ext_iff.mpr ?_
  intro e; simp; constructor
  intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, ⟨h2, h3⟩⟩
  intro ⟨h1, ⟨h2, h3⟩⟩; exact ⟨⟨h1, h2⟩, h3⟩

-- Factor out the (factorization p + 1) from the product over prime factors excluding P'.
lemma lemma12 ( n p : ℕ ) ( P' : Finset ℕ ) ( hp : p ∉ P' )
: ∏ p ∈ (n.primeFactors \ P'), (n.factorization p + 1)
= (n.factorization p + 1) * ∏ p ∈ (n.primeFactors \ (P' ∪ {p})), (n.factorization p + 1) := by 
  by_cases hp' : p ∈ n.primeFactors \ P'
  {
    rw [Finset.prod_eq_mul_prod_diff_singleton hp']; congr 2
    exact lemma11 n.primeFactors P' {p}
  }
  {
    rw [lemma1 _ p hp']
    rw [show (n.factorization p + 1) = 1 by {
      simp
      exact not_mem_support_iff.mp <| by {
        simp at *
        intro pp hn
        have h := hp' pp hn
        by_contra nh
        exact hp (h nh)
      }
    }, one_mul]
    congr 1
    exact lemma11 n.primeFactors P' {p}
  }

-- The divisor-count function τ(n) equals the product over all prime exponents plus one.
lemma lemma13 : ∀ n ≠ 0, τ n = n.factorization.prod (λ _ e => e + 1) := by 
  intro n hn; unfold τ
  rw [sigma_zero_apply, Nat.card_divisors hn, @prod_factorization_eq_prod_primeFactors]

-- Compute the divisor count τ of (p₁^k₁ * n / p₂^k₂), expressing it in terms of factorization of n.
lemma lemma14 ( n p₁ p₂ k₁ k₂ : ℕ ) ( pp₁ : p₁.Prime ) ( pp₂ : p₂.Prime ) ( hpp : p₁ ≠ p₂ )
( hn : n ≠ 0 ) ( hk₂ : p₂ ^ k₂ ∣ n ) : τ (p₁ ^ k₁ * n / p₂ ^ k₂) =
(n.factorization p₁ + k₁ + 1) * (n.factorization p₂ - k₂ + 1) *
∏ p ∈ n.primeFactors \ {p₁, p₂}, (n.factorization p + 1) := by
  obtain ⟨n', hn'⟩ := hk₂
  have hn'' : n' ≠ 0 := by {
    by_contra nh
    rw [nh, mul_zero] at hn'
    rw [hn'] at hn
    contradiction
  }
  have h12 : ({p₁, p₂}:Finset ℕ) = {p₁} ∪ {p₂} := by rfl
  rw [hn', Nat.mul_left_comm, Nat.mul_div_right _ <| by {
    refine Nat.pow_pos ?_
    exact zero_lt_of_ne_zero pp₂.ne_zero
  }]
  rw [lemma13 _ (by {
    refine Nat.mul_ne_zero ?_ hn''
    refine pow_ne_zero k₁ pp₁.ne_zero
  }), @prod_factorization_eq_prod_primeFactors]
  rw [lemma7 k₂ p₂ n' pp₂ <| zero_lt_of_ne_zero hn'',
  Nat.add_sub_cancel, lemma8 k₂ n' p₂ p₁ pp₂ <| Ne.symm <| hpp]
  rw [h12, ← lemma11, sdiff_right_comm,
  lemma10 p₂ k₂ pp₂, sdiff_right_comm, lemma11, ← h12]
  rw [← @Finset.sdiff_empty _ _ (p₁ ^ k₁ * n').primeFactors,
  lemma12 (p₁ ^ k₁ * n') p₁ _ <| Finset.not_mem_empty p₁,
  lemma7 k₁ p₁ n' pp₁ <| zero_lt_of_ne_zero hn'', mul_assoc]; congr 1
  rw [Finset.empty_union, lemma12 (p₁ ^ k₁ * n') p₂ _ <| Finset.not_mem_singleton.mpr (Ne.symm hpp),
  lemma8 k₁ n' p₁ p₂ pp₁ hpp]; congr 1
  rw [← lemma11, lemma10 p₁ k₁ pp₁,
  lemma11, ← h12]
  apply lemma2
  intro p hp; simp at hp
  obtain ⟨⟨pp, ⟨hp, _⟩⟩, ⟨hp1, hp2⟩⟩ := hp
  rw [lemma8 k₁ n' p₁ p pp₁ <| Ne.symm <| hp1,
  lemma8 k₂ n' p₂ p pp₂ <| Ne.symm <| hp2]


lemma lemma15 ( m n : ℕ+ ) { f : ℕ+ -> ℕ } ( h : ∀ n, f n ≤ f (n + 1) ) : m ≤ n -> f m ≤ f n := by 
  intro h
  cases' m with m hm; cases' n with n hn
  have h' : m ≤ n := h
  rw [show (⟨n, hn⟩:ℕ+) = ⟨m + (n - m), by {
    simp_all only [add_tsub_cancel_of_le]
  }⟩ by {
    simp_all only [add_tsub_cancel_of_le]
  }]; clear h
  obtain ⟨d, hd⟩ := show ∃ d, d = n - m by exact ⟨n - m, rfl⟩
  simp only [← hd]
  have hmd : 0 < m + d := by {
    subst hd
    simp_all only [add_tsub_cancel_of_le]
  }
  rw [show (⟨m + d, _⟩:ℕ+) = ⟨m + d, hmd⟩ by rfl]; clear hd h' hn n
  induction d with
  | zero => simp_all only [add_zero, le_refl]
  | succ d' ih => {
    apply (ih <| by simp_all only [add_pos_iff, true_or, ge_iff_le, forall_true_left, zero_lt_one, or_true, or_self]).trans
    exact h ⟨m + d', by simp_all only [add_pos_iff, true_or, ge_iff_le, forall_true_left, zero_lt_one, or_true, or_self]⟩
  }


theorem number_theory_604740 { a : ℕ⁺ -> ℕ } ( ha1 : a ⟨1, by decide⟩ = 2 )
( ha : ∀ n : ℕ⁺, a n < a (n + 1) )
( has: ∀ n : ℕ⁺, τ (a n) < τ (a (n + 1)))
( ham: ∀ n : ℕ⁺, ∀ m, τ (a n) < τ m -> a (n + 1) ≤ m)
: ∃ N, ∀ n > N, 2 * a (n + 1) ≠ 3 * a n := by 
  let e₁ : ℕ⁺ → ℕ := λ n => Nat.factorization (a n) 2
  let e₂ : ℕ⁺ → ℕ := λ n => Nat.factorization (a n) 3

  have e₁_eta : ∀ n, Nat.factorization (a n) 2 = e₁ n := λ n => by rfl
  have e₂_eta : ∀ n, Nat.factorization (a n) 3 = e₂ n := λ n => by rfl

  have han : ∀ n, a n ≠ 0 := by {
    intro n
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    exact (show 0 < 1 by decide).trans <| by {
      cases' n with n hn
      induction n with
      | zero => contradiction
      | succ n' ih => {
        match n' with
        | 0 => rw [ha1]; decide
        | succ n'' => exact ih (zero_lt_succ n'') |>.trans<| ha ⟨n''.succ, _⟩
      }
    }
  }
  have h32 : ∀ n, n = 3 ^ 0 * n / 2 ^ 0 := by {
    intro n
    refine Nat.eq_div_of_mul_eq_right ?_ rfl
    exact Ne.symm (zero_ne_add_one 0)
  }
  -- Each aₙ is minimal amongst all positive integers having the same number of positive divisors as aₙ.
  have h1 : ∀ (n : ℕ⁺) (m : ℕ), τ m = τ (a n) -> a n ≤ m := by {
    intro ⟨n, hn⟩ m hm
    match n with
    | 0 => contradiction
    | succ n' => {
      by_contra nh
      rw [@Nat.not_le] at nh
      match n' with
      | 0 => {
        rw [ha1] at nh hm
        rw [@Nat.lt_add_one_iff_lt_or_eq] at nh
        rw [@lt_one_iff] at nh
        rcases nh with nh | nh <;> simp [nh] at hm
        contradiction
        contradiction
      }
      | succ n'' => {
        have h1 := has ⟨n''.succ, zero_lt_succ n''⟩
        rw [show (⟨n''.succ, zero_lt_succ n''⟩:ℕ⁺) + 1 = ⟨n''.succ.succ, hn⟩ by rfl, ← hm] at h1
        have h2 := ham _ _ h1
        revert h2; simp
        exact nh
      }
    }
  }
  -- Proof. Suppose, if possible, that for some n
  -- some positive integer b < aₙ, has the same number of positive divisors as aₙ.
  have h1' : ∀ n : ℕ⁺, ∀ p, p.Prime -> p ∣ a n -> p ≤ 2 ^ (e₁ n + 1) := by {
    intro n p pp hpm
    by_contra nh
    rw [@Nat.not_le] at nh
    have hp2 : 2 < p := by {
      apply Nat.lt_of_le_of_lt ?_ nh
      refine Nat.le_self_pow ?_ 2
      exact Ne.symm (zero_ne_add_one (e₁ n))
    }
    have ⟨M', hM'⟩ := ordProj_dvd (a n) p
    have ⟨M, hM⟩ : 2 ^ e₁ n ∣ M' := by {
      have h : 2 ^ e₁ n ∣ a n := by exact ordProj_dvd (a n) 2
      rw [hM'] at h
      refine @Nat.Coprime.dvd_of_dvd_mul_left (2 ^ e₁ n) _ M' ?_ h
      refine Coprime.pow_left (e₁ n) ?_
      refine Coprime.pow_right _ ?_
      refine (coprime_primes prime_two pp).mpr ?_
      exact Nat.ne_of_lt hp2
    }
    have hM'₀: M'≠ 0 := by {
      by_contra nh; simp [nh] at hM'
      exact han n hM'
    }
    have hM₀ : M ≠ 0 := by {
      by_contra nh; simp [nh] at hM
      exact hM'₀ hM
    }
    set eᵢ:= (a n).factorization p with heᵢ
    -- Let b = 2^e ⋅ 1 ⋅ k, where k is odd and e is the integer provided by (1).
    set b := 2 ^ (eᵢ * (e₁ n + 1) + e₁ n) * M with hb
    -- Then e ≥ e₁(n) > 0, so
    -- 2^{e₁(n)(e₂(n)+1)+e} ⋅ aₙ / pᵢ^{e₁(n)} is a positive integer with the same number of
    -- positive divisors as aₙ, but smaller than aₙ. This contradicts Lemma 1.
    have Hb : τ b = τ (a n) := by {
      have h2ₘ : ¬ 2 ∣ M := by {
        by_contra nh
        obtain ⟨M2, h2⟩ := nh
        rw [h2, ← mul_assoc, ← Nat.pow_succ] at hM; clear h2
        rw [hM] at hM'
        have nh := Eq.refl <| e₁ n
        nth_rw 1 [← e₁_eta] at nh
        rw [hM'] at nh
        rw [lemma8 _ _ _ _ pp <| Ne.symm <| Nat.ne_of_lt hp2] at nh
        rw [lemma7 _ _ _ prime_two <| by {
          by_contra nh
          rw [@Nat.not_lt, Nat.le_zero] at nh
          rw [nh, mul_zero, mul_zero] at hM'
          exact han n hM'
        }, Nat.succ_eq_add_one, ← add_assoc, add_right_comm] at nh
        simp at nh
      }
      have hpₘ : ¬ p ∣ M := by {
        by_contra nh
        obtain ⟨Mp, hp⟩ := nh
        rw [hp, ← mul_assoc] at hM; clear hp
        rw [hM] at hM'
        have nh := Eq.refl <| eᵢ
        nth_rw 1 [heᵢ] at nh
        rw [hM'] at nh
        rw [lemma7 _ _ _ pp <| by {
          by_contra nh
          rw [@Nat.not_lt, Nat.le_zero] at nh
          rw [nh, mul_zero] at hM'
          exact han n hM'
        }, mul_assoc] at nh
        rw [lemma8 _ _ _ _ prime_two <| Nat.ne_of_lt hp2] at nh
        rw [lemma5 _ _ pp <| by {
          by_contra nh
          rw [@Nat.not_lt, Nat.le_zero] at nh
          rw [nh, mul_zero, mul_zero] at hM'
          exact han n hM'
        }] at nh
        simp at nh
      }
      have hp2' : p ∉ ({2}:Finset ℕ) := by exact Finset.not_mem_of_max_lt hp2 rfl
      rw [hM', hb, hM, ← mul_assoc, mul_comm (p ^ eᵢ)]
      rw [lemma13 _ <| by {
        refine Nat.mul_ne_zero ?_ hM₀
        refine pow_ne_zero _ prime_two.ne_zero
      }, @prod_factorization_eq_prod_primeFactors]
      rw [lemma13 _ <| by {
        refine Nat.mul_ne_zero ?_ hM₀
        refine Nat.mul_ne_zero ?_ ?_
        refine pow_ne_zero _ prime_two.ne_zero
        refine pow_ne_zero _ pp.ne_zero
      }, @prod_factorization_eq_prod_primeFactors]
      rw [← @Finset.sdiff_empty _ _ (2 ^ (eᵢ * (e₁ n + 1) + e₁ n) * M).primeFactors,
      ← @Finset.sdiff_empty _ _ (2 ^ e₁ n * p ^ eᵢ * M).primeFactors]
      rw [lemma12 _ 2 _ (Finset.not_mem_empty 2),
      lemma12 (2 ^ e₁ n * p ^ eᵢ * M) 2 _ (Finset.not_mem_empty 2),
      Finset.empty_union,
      lemma12 _ p _ hp2', lemma12 (2 ^ e₁ n * p ^ eᵢ * M) p _ hp2']
      rw [lemma7 (eᵢ * (e₁ n + 1) + e₁ n) 2 M prime_two (zero_lt_of_ne_zero hM₀),
      factorization_eq_zero_of_not_dvd h2ₘ, zero_add,
      lemma8 (eᵢ * (e₁ n + 1) + e₁ n) M 2 p prime_two (Nat.ne_of_lt hp2),
      factorization_eq_zero_of_not_dvd hpₘ, zero_add, one_mul]
      rw [← lemma11, lemma10 2 _ prime_two,
      lemma11]
      rw [mul_assoc, lemma7 _ 2 (p ^ eᵢ * M) prime_two <|
      zero_lt_of_ne_zero <| Nat.mul_ne_zero (pow_ne_zero (eᵢ) pp.ne_zero) hM₀,
      factorization_eq_zero_of_not_dvd <| by {
        exact Nat.Prime.not_dvd_mul prime_two (by {
          refine (Nat.Prime.coprime_iff_not_dvd prime_two).mp ?_
          refine Coprime.pow_right (eᵢ) ?_
          refine (coprime_primes prime_two pp).mpr ?_
          exact Nat.ne_of_lt hp2
        }) h2ₘ
      }, zero_add, lemma8 _ _ _ _ prime_two (Nat.ne_of_lt hp2),
      lemma7 _ _ _ pp (zero_lt_of_ne_zero hM₀), factorization_eq_zero_of_not_dvd hpₘ,
      zero_add, ← mul_assoc]
      rw [← lemma11 (2 ^ e₁ n * (p ^ eᵢ * M)).primeFactors,
      lemma10 2 _ prime_two, sdiff_right_comm,
      lemma10 p _ pp,
      sdiff_right_comm, lemma11]
      rw [show (eᵢ * (e₁ n + 1) + e₁ n + 1) = (e₁ n + 1) * (eᵢ + 1) by ring]; congr 1
      apply lemma2; intro pᵢ hp
      simp at hp
      obtain ⟨⟨ppᵢ, ⟨hpᵢ, _⟩⟩, ⟨hp2ᵢ, hppᵢ⟩⟩ := hp
      rw [lemma8 _ _ _ _ prime_two <| Ne.symm <| hp2ᵢ,
      lemma8 _ _ _ _ prime_two <| Ne.symm <| hp2ᵢ,
      lemma8 _ _ _ _ pp <| Ne.symm <| hppᵢ]
      -- Consequently, no special term is divisible by a prime exceeding 2^{e₁+1}.
    }
    have Hb' : b < a n := by {
      rw [hb, Nat.pow_add, mul_assoc, ← hM]
      rw [hM']
      refine Nat.mul_lt_mul_of_pos_right (by {
        rw [mul_comm, Nat.pow_mul]
        refine Nat.pow_lt_pow_left nh ?_
        by_contra nh
        have hpm' : ¬ p ∣ a n := by {
          by_contra nh'
          obtain ⟨q, hq⟩ := nh'
          rw [heᵢ, hq, lemma5 _ _ pp <| by {
            by_contra nh
            rw [not_lt_eq, Nat.le_zero] at nh
            rw [nh, mul_zero] at hq
            exact han n hq
          }] at nh
          contradiction
        }
        exact hpm' hpm
      }) ?_
      refine zero_lt_of_ne_zero hM'₀
    }
    have nh := h1 n b Hb
    linarith
  }
  -- To prove (1), it is sufficient to show that, as aₙ runs through the special terms,
  -- the exponents e₁(n) are bounded from above.
  by_contra nh; simp at nh
  have nH : ∀ (n : ℕ+), ∃ n', n < n' ∧ 2 * a (n' + 1) = 3 * a n' := nh; clear nh
  have h2': ∀ M, ∃ N, ∀ n ≥ N, M < e₁ n := by {
    intro M; by_contra nh; simp at nh
    have nh : ∃ M, ∀ N, ∃ n, N ≤ n ∧ τ (a n) < M := by {
      have H : ∀ M, ∃ M', ∀ n, e₁ n ≤ M -> τ (a n) ≤ M' := by {
        clear nh nH h1 M; intro M
        simp only [← e₁_eta] at *; clear e₁_eta e₁ e₂_eta e₂ ha h32
        {
          -- First prove that for any prime p > 2,
          -- there exists a bound Eₚ on the exponent of p in a(n),
          -- assuming the exponent of 2 in a(n) is bounded by M
          have hEp : ∀ p > 2, p.Prime -> ∃ Eₚ, ∀ n, (a n).factorization 2 ≤ M → (a n).factorization p ≤ Eₚ := by {
            by_contra nh; simp at nh
            obtain ⟨p, hp2, pp, hp⟩ := nh
            have ⟨p₀, hp₀, pp₀⟩ := Nat.exists_infinite_primes (2 ^ (M + 2))
            have ⟨k, hk⟩ := pow_unbounded_of_one_lt p₀ (show 1 < p by linarith)
            have ⟨n', hn', hnp⟩ := hp (2 * k + 1)
            have ⟨n, hn1⟩ : ∃ n, n' = n + 1 := by {
              cases' n' with n' zero_lt_n'
              have h2 : 2 ≤ n' := by {
                by_contra nh; rw [@Nat.not_le] at nh
                simp [@Nat.le_iff_lt_or_eq, @Nat.lt_add_one_iff_lt_or_eq] at nh
                rcases nh with nh | nh
                linarith
                subst nh
                have nh : 2 * k + 1 < (a ⟨1, by decide⟩).factorization p := hnp
                rw [ha1, factorization_eq_zero_of_lt hp2] at nh
                linarith
              }
              match n' with
              | 0 => linarith
              | 1 => linarith
              | n'' + 1 + 1 => {
                use ⟨n'' + 1, zero_lt_succ _⟩
                rfl
              }
            }; subst hn1

            -- Define b as p₀ * a(n + 1) / p^k
            set b := p₀ * (a (n + 1)) / (p ^ k) with hb
            have ⟨an', han'⟩ : p ^ k ∣ a (n + 1) := by {
              refine (Prime.pow_dvd_iff_dvd_ordProj pp (han (n + 1))).mpr ?_
              refine Nat.pow_dvd_pow p ?_
              linarith
            }
            have hpp₀ : p ≠ p₀ := by {
              have h := h1' (n + 1) p pp <| by {
                by_contra nh
                rw [Nat.factorization_eq_zero_of_not_dvd nh] at hnp
                contradiction
              }
              have hp := h.trans (show 2 ^ ((a (n + 1)).factorization 2 + 1) ≤ 2 ^ (M + 1) by {
                apply Nat.pow_le_pow_right Nat.zero_lt_two; linarith
              })
              have nh' : 2 ^ (M + 1) < 2 ^ (M + 2) := by {
                apply Nat.pow_lt_pow_right Nat.one_lt_two; linarith
              }
              linarith
            }
            -- Show τ(a(n+1)) < τ(b) using factorization properties and monotonicity
            have Hb : τ (a (n + 1)) < τ b := by {
              have han₀ : 0 < an' := by {
                by_contra nh; simp at nh; simp [nh] at han'
                exact han (n + 1) han'
              }
              rw [hb]; clear hb b
              rw [han', mul_left_comm, Nat.mul_div_right _ <| pow_pos (zero_lt_of_lt hp2) k]
              rw [lemma13 _ <| han'.symm ▸ han (n + 1), @prod_factorization_eq_prod_primeFactors]
              rw [lemma13 _ <| by {
                by_contra nh
                simp_all only [PNat.mk_ofNat, ne_eq, _root_.mul_eq_zero]
                cases nh with
                | inl h =>
                  subst h
                  simp_all only [nonpos_iff_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
                    not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero]
                | inr h_1 =>
                  subst h_1
                  simp_all only [mul_zero, Nat.factorization_zero, coe_zero, Pi.zero_apply, _root_.zero_le, not_lt_zero']
              }, @prod_factorization_eq_prod_primeFactors]
              rw [← @Finset.sdiff_empty _ _ (p ^ k * an').primeFactors, ← @Finset.sdiff_empty _ _ (p₀ * an').primeFactors]
              rw [lemma12 _ p _ (Finset.not_mem_empty p),
              lemma12 _ p₀ _ (by simp; exact Ne.symm hpp₀),
              lemma7 k p an' pp han₀,
              lemma8 k an' p p₀ pp hpp₀]
              rw [lemma12 (p₀ * an') p _ (Finset.not_mem_empty p),
              lemma12 (p₀ * an') p₀ _ (by simp; exact Ne.symm hpp₀),
              lemma6 an' p₀ p pp₀ <| Ne.symm <| hpp₀,
              lemma5 p₀ an' pp₀ han₀]
              rw [Finset.empty_union, ← lemma11,
              lemma10 p k pp, ← lemma11,
              sdiff_right_comm (p₀ * an').primeFactors, lemma9 p₀ pp₀,
              sdiff_right_comm, @lemma2 _ _ _ _ _ _ (λ p => (p₀ * an').factorization p + 1) <| by {
                intro pᵢ hpᵢ; simp at hpᵢ
                obtain ⟨⟨⟨ppᵢ, ⟨hpᵢ, _⟩⟩, hpᵢp₀⟩, hpᵢp⟩ := hpᵢ; dsimp
                rw [lemma8, lemma6]
                exact pp₀
                exact Ne.symm hpᵢp₀
                exact pp
                exact Ne.symm hpᵢp
              }, ← mul_assoc, ← mul_assoc, mul_lt_mul_right <| by {
                apply lemma3; intro i _
                exact zero_lt_succ ((p₀ * an').factorization i)
              }]
              rw [show an'.factorization p₀ = 0 by {
                apply Nat.factorization_eq_zero_of_not_dvd
                by_contra nh
                have h := h1' (n + 1) p₀ pp₀ (by {
                  rw [han']
                  exact Dvd.dvd.mul_left nh (p ^ k)
                })
                have nh := h.trans (show 2 ^ ((a (n + 1)).factorization 2 + 1) ≤ 2 ^ (M + 1) by {
                  apply Nat.pow_le_pow_right Nat.zero_lt_two; linarith
                })
                have nh' : 2 ^ (M + 1) < 2 ^ (M + 2) := by {
                  apply Nat.pow_lt_pow_right Nat.one_lt_two; linarith
                }
                linarith
              }]
              ring_nf
              rw [add_right_comm, mul_two, ← add_assoc]; simp
              rw [han', lemma7 k p an' pp han₀] at hnp
              linarith
            }
            have Hb' : τ (a n) < τ b := has n |>.trans Hb
            have nh := ham _ _ Hb'
            rw [hb, han', ← mul_assoc, mul_comm p₀, mul_assoc] at nh
            rw [Nat.mul_div_right _ <| pow_pos (zero_lt_of_lt hp2) k] at nh
            rw [mul_le_mul_iff_of_pos_right] at nh
            linarith
            by_contra nh; simp at nh; simp [nh] at han'
            exact han (n + 1) han'
          }
          -- Define function E that bounds factorization exponents for each prime p
          set E : (p : ℕ) -> { Eₚ // ∀ n, (a n).factorization 2 ≤ M → (a n).factorization p ≤ Eₚ } := by {
            intro p
            by_cases hp : p > 2
            {
              by_cases pp : p.Prime
              {
                have h := hEp p hp pp
                let E := h.choose
                let hE := h.choose_spec
                exact ⟨E, hE⟩
              }
              exact ⟨0, by {
                intro n _
                simp_all only [ne_eq, gt_iff_lt, not_false_eq_true, factorization_eq_zero_of_non_prime, le_refl]
              }⟩
            }
            {
              rw [not_lt_eq] at hp
              by_cases hp2 : p = 2
              rw [hp2]
              exact ⟨M, λ _ => id⟩
              by_cases hp1 : p = 1
              rw [hp1]
              exact ⟨0, by {
                intro n hn
                rw [factorization_one_right]
              }⟩
              by_cases hp0 : p = 0
              rw [hp0]
              exact ⟨0, by {
                intro n hn
                rw [factorization_zero_right]
              }⟩
              simp [@Nat.le_iff_lt_or_eq, @Nat.lt_add_one_iff_lt_or_eq, hp2, hp1, hp0] at hp
            }
          }
          -- Define M' as the product over primes ≤ 2^(M+1) of (E p + 1)
          set M' := ∏ p ≤ 2 ^ (M + 1), ((E p).1 + 1) with hM'
          use M'; intro n hn
          rw [lemma13 (a n) (han n), @prod_factorization_eq_prod_primeFactors, hM']
          clear ha1 has ham han M' hM'
          -- Show the prime factors of a(n) are all ≤ 2^(M+1) using assumption h1'
          apply lemma4
          {
            refine Finset.subset_iff.mpr ?_
            intro p hp; simp at hp
            have h := h1' n p hp.left hp.right.left |>.trans
              (show 2 ^ ((a n).factorization 2 + 1) ≤ 2 ^ (M + 1) by {
                apply Nat.pow_le_pow_right Nat.zero_lt_two; linarith
              })
            refine Finset.mem_Iio.mpr ?_
            linarith
          }
          simp
          simp; exact λ p => (E p).2 n hn
        }
      }
      have ⟨M', hM'⟩ := H M
      use M' + 1
      intro N
      have ⟨n, hn, hen⟩ := nh N
      use n; constructor
      exact hn
      have h := hM' n hen
      exact Order.lt_add_one_iff.mpr h
    }
    revert nh; simp
    have h : ∀ N, ∃ n, N < τ (a n) := by {
      intro N
      use ⟨N + 1, Nat.zero_lt_succ N⟩
      induction N with
      | zero => {rw [ha1]; decide}
      | succ N' ih => {
        rw [@lt_iff_add_one_le] at ih
        apply Nat.lt_of_le_of_lt ih
        exact has ⟨N' + 1, _⟩
      }
    }
    intro N
    obtain ⟨n, hn⟩ := h N
    use n; intro n' hn'
    apply Nat.le_of_lt
    apply Nat.lt_of_lt_of_le hn
    apply @lemma15 n n' (λ n => τ (a n)) (by {
      intro n; have h := has n; simp only
      exact Nat.le_of_succ_le h
    }) hn'
  }
  -- Then, Lemma 2 shows that such an upper bound e suits all primes.
  have h2 : ∃ M, ∃ N, ∀ n ≥ N, 2 * a (n + 1) = 3 * a n -> e₁ n ≤ M ∧ e₂ n ≤ M := by {
    have h2_1₀ : ∀ n, 2 * a (n + 1) = 3 * a n -> a (n + 1) = 3 * a n / 2 := by {
      intro n hn
      rw [← @Nat.mul_left_inj 2 _ _ <| Ne.symm (Nat.zero_ne_add_one 1)]
      rw [Nat.mul_comm, hn, Eq.comm, mul_comm, Nat.mul_div_eq_iff_dvd]
      use a (n + 1)
      exact hn.symm
    }
    have h2_1₁ : ∀ n, 2 * a (n + 1) = 3 * a n -> 2 ∣ a n := by {
      intro n hn
      refine Coprime.dvd_of_dvd_mul_left (show Nat.Coprime 2 3 by rfl) ?_
      exact ⟨a (n + 1), hn.symm⟩
    }
    -- Consider a large enough special aₙ.
    -- The condition τ(aₙ) < τ(aₙ₊₁) is then equivalent to
    -- (e₁(n)+1)(e₂(n)+1) < e₁(n)(e₂(n)+2)
    have h2_1 : ∀ n, 2 * a (n + 1) = 3 * a n -> (e₁ n + 1) * (e₂ n + 1) < e₁ n * (e₂ n + 2) := by {
      intro n hn
      have h := h2_1₀ n hn ▸ has n
      rw [show 3 * a n / 2 = 3 ^ 1 * a n / 2 ^ 1 by exact rfl] at h
      nth_rewrite 1 [h32 (a n)] at h
      rw [lemma14 (a n) 3 2 0 0 prime_three prime_two (by decide) (han n) <| by simp,
      lemma14 (a n) 3 2 1 1 prime_three prime_two (by decide) (han n) <| by {
        simp [h2_1₁ n hn]
      }, Nat.mul_lt_mul_right <| by {
        apply lemma3; intro i _
        exact zero_lt_succ ((a n).factorization i)
      }] at h
      rw [show (a n).factorization 2 - 1 + 1 = (a n).factorization 2 by {
        refine Nat.sub_add_cancel ?_
        refine (Prime.dvd_iff_one_le_factorization prime_two <| han n).mp<| h2_1₁ n hn
      }] at h
      rw [e₁_eta, e₂_eta, mul_comm, mul_comm (e₂ n + 1 + 1)] at h
      exact h
    }
    have ⟨N, h2_1'⟩ : ∃ N, ∀ n ≥ N, 2 * a (n + 1) = 3 * a n -> 16 ∣ a n := by {
      obtain ⟨N, hN⟩ := h2' 3
      use N; intro n hn _
      exact (padicValNat_dvd_iff_le (han n)).mpr<| hN n hn
    }
    use 17; use N; intro n hnN hn
    have h2_2 : (2 * e₁ n ≤ 3 * e₂ n + 7) ∧ (2 * e₂ n ≤ e₁ n + 1) := by {
      have h2_2_1 : 2 * e₁ n ≤ 3 * e₂ n + 7 := by {
        -- The latter implies that aₙ is divisible by 8,
        -- for either e₁(n) ≥ 3 or aₙ is a large enough power of 2.
        have h2_2_1'' : 8 ∣ a n := by {
          have ⟨n', hn'⟩ := h2_1' n hnN hn
          exact ⟨2 * n', by {
            rw [hn']
            ring
          }⟩
        }
        have h2_2_1' : 3 ≤ (a n).factorization 2 :=
          (Prime.pow_dvd_iff_le_factorization prime_two (han n)).mp h2_2_1''
        -- Note that 9aₙ/8 is an integer strictly between aₙ and aₙ₊₁.
        -- So τ(9aₙ/8) ≤ τ(aₙ), which is equivalent to:
        -- (e₁(n)-2)(e₂(n)+3) ≤ (e₁(n)+1)(e₂(n)+1)
        have h2_2_1_1 : τ (9 * a n / 8) ≤ τ (a n) := by {
          by_contra nh
          rw [@Nat.not_le] at nh
          have h := h2_1₀ n hn ▸ ham n _ nh
          revert h
          simp
          refine (Nat.div_lt_iff_lt_mul <| by decide).mpr ?_
          rw [show 3 * a n / 2 * 8 = 12 * a n by {
            rw [show 8 = 2 * 4 by rfl, ← mul_assoc,
            Nat.div_mul_cancel <|
              (Coprime.dvd_mul_left (h32 (Nat.gcd 2 3))).mpr (h2_1₁ n hn)]
            ring
          }]
          have h : 0 < a n := zero_lt_of_ne_zero (han n)
          linarith
        }
        have h2_2_1_2 : (e₁ n - 2) * (e₂ n + 3) ≤ (e₁ n + 1) * (e₂ n + 1) := by {
          nth_rw 2 [h32 (a n)] at h2_2_1_1
          rw [show 9 * a n / 8 = 3 ^ 2 * a n / 2 ^ 3 by exact rfl] at h2_2_1_1
          rw [lemma14 (a n) 3 2 2 3 prime_three prime_two (by decide) (han n) <| h2_2_1'',
          lemma14 (a n) 3 2 0 0 prime_three prime_two (by decide) (han n) <| by simp,
          mul_le_mul_iff_of_pos_right <| by {
            apply lemma3; intro i _
            exact zero_lt_succ ((a n).factorization i)
          }] at h2_2_1_1
          rw [show (a n).factorization 2 - 3 + 1 = (a n).factorization 2 - 2 by {
            refine Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add h).mp) ?_ rfl)
            exact le_sub_of_add_le h2_2_1'
          }] at h2_2_1_1
          rw [mul_comm, mul_comm (e₂ n + 0 + 1)] at h2_2_1_1
          exact h2_2_1_1
        }
        rw [← @Nat.add_le_add_iff_right _ _ (2 * (e₂ n + 3)), ← add_mul,
        Nat.sub_add_cancel <| le_of_succ_le h2_2_1'] at h2_2_1_2
        linarith
      }
      -- So 2e₁(n) ≤ 3e₂(n)+7. This shows that aₙ is divisible by 3,
      -- for otherwise, letting aₙ run through the special terms,
      -- 3 would be an upper bound for all but finitely many e₁(n)
      have h2_1'' : 3 ∣ a n := by {
        have hl := (@Prime.pow_dvd_iff_le_factorization _ 4 _ prime_two (han n)).mp
          (h2_1' n hnN hn)
        have hr := h2_2_1
        have hl : 2 * 4 ≤ 2 * (a n).factorization 2 := by linarith
        -- rw [← @mul_le_mul_left ℕ 2] at hl
        have h := le_trans hl hr
        have h' : 1 ≤ e₂ n := by {
          by_contra nh
          rw [@Nat.not_le, @lt_one_iff] at nh
          rw [nh] at h
          linarith
        }
        exact dvd_of_one_le_padicValNat h'
      }
      -- So 2e₂(n) - 1 ≤ e₁(n)
      have h2_2_2 : 2 * e₂ n ≤ e₁ n + 1 := by {
        have h2_2_2' : 1 ≤ (a n).factorization 3 :=
          (Prime.pow_dvd_iff_le_factorization prime_three (han n)).mp h2_1''
        -- Thus, 4aₙ/3 is another integer strictly between aₙ and aₙ₊₁. Again,
        -- τ(4aₙ/3) ≤ τ(aₙ), i.e.:
        -- (e₁(n)+3)e₂(n) ≤ (e₁(n)+1)(e₂(n)+1)
        have h2_2_2_2 : τ (4 * a n / 3) ≤ τ (a n) := by {
          by_contra nh
          rw [@Nat.not_le] at nh
          have h := h2_1₀ n hn ▸ ham n _ nh
          revert h
          simp
          refine (Nat.div_lt_iff_lt_mul <| by decide).mpr ?_
          rw [← @mul_lt_mul_iff_of_pos_right ℕ 2 _ _ _ _ _ _ _ <| by decide, mul_right_comm _ 3,
          show 3 * a n / 2 * 2 * 3 = 9 * a n by {
            rw [Nat.div_mul_cancel <|
              (Coprime.dvd_mul_left (h32 (Nat.gcd 2 3))).mpr (h2_1₁ n hn)]
            ring
          }]
          have h : 0 < a n := zero_lt_of_ne_zero (han n)
          linarith
        }
        have h2_2_2_3 : (e₁ n + 3) * e₂ n ≤ (e₁ n + 1) * (e₂ n + 1) := by {
          nth_rw 2 [h32 (a n)] at h2_2_2_2
          rw [show 4 * a n / 3 = 2 ^ 2 * a n / 3 ^ 1 by exact rfl] at h2_2_2_2
          rw [lemma14 (a n) 2 3 2 1 prime_two prime_three (by decide) (han n) <| by {
            exact dvd_of_one_le_padicValNat h2_2_2'
          },
          lemma14 (a n) 3 2 0 0 prime_three prime_two (by decide) (han n) <| by simp,
          show {3, 2} = {2, 3} by decide,
          mul_le_mul_iff_of_pos_right <| by {
            apply lemma3; intro i _
            exact zero_lt_succ ((a n).factorization i)
          }, mul_comm (e₂ n + 0 + 1)] at h2_2_2_2
          rw [show (a n).factorization 3 - 1 + 1 = (a n).factorization 3 by {
            refine Eq.symm ((fun h => (Nat.sub_eq_iff_eq_add h).mp) ?_ rfl)
            exact (Prime.dvd_iff_one_le_factorization prime_three <| han n).mp<| h2_1''
          }] at h2_2_2_2
          exact h2_2_2_2
        }
        linarith
      }
      exact ⟨h2_2_1, h2_2_2⟩
    }
    -- Combine this with the inequality in the previous paragraph to write:
    -- 4e₂(n) - 2 ≤ 2e₁(n) ≤ 3e₂(n) + 7 ⇒ e₂(n) ≤ 9
    have h2_2_2 : e₂ n ≤ 9 := by {
      have h := h2_2
      have hr := @Nat.add_le_add_iff_right _ _ 2 |>.mpr<| h.left
      have hl := Nat.mul_le_mul_left 2 <| h.right
      rw [← Nat.mul_add_one] at hr
      have h := hl.trans hr
      linarith
    }
    -- Consequently, 2e₁(n) ≤ 3e₂(n) + 7 ≤ 34 ⇒ e₁(n) ≤ 17
    have h2_2_3 : e₁ n ≤ 17 := by {
      have h := h2_2 |>.left.trans<| show 3 * e₂ n + 7 ≤ 34 by {
        have h := h2_2_2
        linarith
      }
      linarith
    }
    exact ⟨h2_2_3, h2_2_2 |>.trans (show 9 ≤ 17 by exact Nat.le_of_ble_eq_true rfl)⟩
  }
  -- Showing that e = 17 is suitable for (1) to hold. This establishes (1) and completes the solution.
  {
    obtain ⟨M, N, hN⟩ := h2
    have ⟨N', hN'⟩ := h2' M
    have ⟨n', hn', nh⟩ := nH (N + N')
    have hn' : (↑N:ℕ) + ↑N' < ↑n' := hn'
    have nh := hN n' (by {
      exact Nat.le_of_succ_le <| Nat.lt_add_of_pos_right N'.2 |>.trans hn'
    }) nh |>.left
    have nh':= hN' n' (by {
      exact Nat.le_of_succ_le <| Nat.lt_add_of_pos_left N.2 |>.trans hn'
    })
    linarith
  }