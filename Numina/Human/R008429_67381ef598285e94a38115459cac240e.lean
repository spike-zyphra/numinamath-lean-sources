import Mathlib
set_option maxHeartbeats 500000
/-24. N1 (BLR) Let $\tau(n)$ denote the number of positive divisors of the positive integer $n$. Prove that there exist infinitely many positive integers $a$ such that the equation  $$ \tau(a n)=n $$  does not have a positive integer solution $n$.-/
theorem number_theory_25178 {τ : ℕ → ℕ} (h : ∀ m, τ m = m.divisors.card) :
{a | 1 ≤ a ∧ ¬ ∃ n, τ (a * n) = n ∧ 1 ≤ n}.Infinite := by
-- We first prove the following auxillary inequalities by induction for later use
  have aux1 : ∀ t q, 1 ≤ t → 2 ≤ q → t + 1 ≤ q ^ t := by
    suffices : ∀ t, 1 ≤ t → t + 1 ≤ 2 ^ t
    · intro t q ht hq
      have := this t ht
      have : 2 ^ t ≤ q ^ t := Nat.pow_le_pow_of_le_left hq t
      linarith
    intro t ht; induction t with
    | zero => simp
    | succ n ih =>
      rw [pow_add, pow_one, mul_two]; apply Nat.add_le_add
      by_cases h' : n < 1; simp at h'; rw [h']; norm_num
      push_neg at h'; apply ih; assumption; exact Nat.one_le_two_pow
  have aux2 : ∀ t q, 2 ≤ t → 3 ≤ q → t + q < q ^ t := by
    intro t q ht hq; induction t with
    | zero => linarith
    | succ t ih =>
      by_cases h' : t < 2; suffices : t = 1
      · rw [this, pow_add, pow_one, show 1+1=2*1 by norm_num]
        nth_rw 3 [show q=q-1+1 by rw [Nat.sub_add_cancel];linarith]
        rw [Nat.mul_add]; apply Nat.add_lt_add_of_lt_of_le
        apply Nat.mul_lt_mul''; any_goals linarith
        rw [Nat.lt_sub_iff_add_lt]; linarith
      linarith; push_neg at h'; replace ih := ih h'
      rw [show t+1+q=t+q+1 by ring, pow_add, pow_one]
      nth_rw 3 [show q=1+(q-1) by rw [Nat.add_sub_cancel'];linarith]
      rw [mul_add, mul_one]; apply Nat.add_lt_add; assumption
      rw [Nat.one_lt_mul_iff]; split_ands
      · apply Nat.pow_pos; linarith
      · rw [Nat.sub_pos_iff_lt]; linarith
      right; rw [Nat.lt_sub_iff_add_lt]; linarith
  have aux3 : ∀ t p q, p ≤ t + 1 → 2 ≤ q → 5 ≤ p → (t + 1) * (1 + p) < q ^ t * p := by
    intro t p q ht hq hp
    suffices : ∀ t p, p ≤ t + 1 → 5 ≤ p → (t + 1) * (1 + p) < 2 ^ t * p
    · have := this t p ht hp
      have : 2 ^ t * p ≤ q ^ t * p := by
        apply Nat.mul_le_mul; exact Nat.pow_le_pow_of_le_left hq t; rfl
      linarith
    intro t p ht hp; induction t with
    | zero => linarith
    | succ t ih =>
      by_cases h' : t + 1 < p
      · have : p = t + 2 := by linarith
        rw [this]; rw [this] at hp; simp at hp
        rw [show (t + 1 + 1) * (1 + (t + 2)) = (t + 3) * (t + 2) by ring]
        rw [mul_lt_mul_iff_of_pos_right, pow_add, pow_one, mul_two]
        apply add_lt_add; apply Nat.lt_pow_self; norm_num
        rw [show 3=2^1+1 by norm_num, show t=1+(t-1) by rw [Nat.add_sub_cancel']; linarith]
        rw [pow_add]; nth_rw 2 [pow_one]; rw [two_mul]
        apply Nat.add_lt_add; rw [Nat.pow_lt_pow_iff_right, Nat.lt_sub_iff_add_lt]
        any_goals linarith
        apply Nat.one_lt_pow; intro h''; rw [Nat.sub_eq_zero_iff_le] at h''; any_goals linarith
      push_neg at h'; replace ih := ih h'
      rw [add_mul, one_mul, pow_add, pow_one, mul_two]
      nth_rw 2 [add_mul]; apply Nat.add_lt_add; assumption
      rw [show 2^t=2^t-1+1 by rw [Nat.sub_add_cancel];apply Nat.one_le_pow; norm_num]
      rw [add_mul, one_mul]; apply Nat.add_lt_add_of_lt_of_le; rw [Nat.one_lt_mul_iff]; split_ands
      · rw [Nat.sub_pos_iff_lt]; apply Nat.one_lt_pow; linarith; norm_num
      · linarith
      · right; linarith
      rfl
-- Define the function of raising to the power of self minus one by pS1
  let pS1 : ℕ → ℕ := fun t => t ^ (t - 1)
-- Prove the key fact that pS1 maps the set of prime numbers not equal to $2$ or $3$ to the set in question,
-- we will show that the equation $τ(p^(p-1)*n)=n$ has no positive solution.
  have key : Set.MapsTo pS1 ({p | Nat.Prime p} \ {2, 3}) {a | 1 ≤ a ∧ ¬ ∃ n, τ (a * n) = n ∧ 1 ≤ n} := by
  -- Rewrite the assumptions and prove some simple facts for later use
    rw [Set.MapsTo]; simp; intro p hp pne2 pne3; push_neg at pne2
    have fp : Fact (Nat.Prime p) := ⟨hp⟩
    have pge3 : 5 ≤ p := by
      by_contra; interval_cases p; any_goals contradiction
  -- Assume that $x$ is a positive solution to the equation in question, rewrite the equation by applying h and Nat.card_divisors
    constructor; simp [pS1]; apply Nat.one_le_pow; linarith
    intro x hx; simp [pS1] at hx; by_contra xne0; push_neg at xne0
    rw [h, Nat.card_divisors] at hx
  -- Isolate $p$ from the set of prime factors and rewrite the product by applying Finset.prod_union
    have : (p ^ (p - 1) * x).primeFactors = ((p ^ (p - 1) * x).primeFactors \ {p}) ∪ {p} := by
      rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left.mpr]
      simp; constructor; assumption; constructor
      · use p^(p-2)*x; nth_rw 3 [← pow_one p]
        rw [← mul_assoc, ← Nat.pow_add]; congr
        rw [← Nat.add_sub_assoc, show 2=1+1 by norm_num, ← Nat.sub_sub]
        rw [Nat.add_sub_cancel_left]; linarith
      constructor; intro; linarith; push_neg; assumption
    rw [this, Finset.prod_union] at hx; simp at hx
  -- Simplify hx by using properties of Nat.factorization
    nth_rw 2 [Nat.factorization_mul] at hx
    rw [Finsupp.add_apply] at hx
    nth_rw 1 [Nat.factorization_def, padicValNat.prime_pow] at hx
    nth_rw 2 [add_comm] at hx; rw [add_assoc, Nat.sub_add_cancel] at hx
    rw [Nat.primeFactors_mul, Finset.union_sdiff_distrib] at hx
    rw [Nat.primeFactors_prime_pow] at hx; simp at hx
    have : ∏ x_1 ∈ x.primeFactors \ {p}, ((p ^ (p - 1) * x).factorization x_1 + 1) = ∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1) := by
      rw [Finset.prod_congr]; rfl; intro q hq; simp at hq
      push_neg at hq; rcases hq with ⟨⟨hq⟩⟩
      have : Fact (Nat.Prime q) := ⟨hq⟩
      rw [Nat.factorization_mul, Finsupp.add_apply]; simp
      right; rw [Nat.factorization_def]; apply padicValNat_primes
      any_goals assumption
      any_goals intro; simp_all
    rw [this] at hx
  -- Prove that $p$ divides $x$
    have pdvdx : p ∣ x := by
      by_contra; suffices : x.factorization p = 0
      · rw [this] at hx; simp at hx
        have : p ∣ x := by
          use (∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1))
          rw [mul_comm]; symm; assumption
        contradiction
      rw [Nat.factorization_eq_zero_iff]; right; left; assumption
  -- Write out the unique prime factorization of $x$ and isolates $p$ from this product
    have facx : x = (∏ q ∈ x.primeFactors \ {p}, q ^ (x.factorization q)) * p ^ (x.factorization p) := by
      have facx := Nat.factorization_prod_pow_eq_self xne0
      rw [Finsupp.prod, Nat.support_factorization] at facx
      have : x.primeFactors = x.primeFactors \ {p} ∪ {p} := by
        rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left.mpr]
        simp; constructor; assumption; constructor; assumption
        push_neg; assumption
      rw [this, Finset.prod_union] at facx; simp at facx
      symm; assumption; apply Finset.sdiff_disjoint
  -- Rewrite $x$ on the RHS of hx by applying this factorization
  -- we will compare the two products and show that the LHS is always less than the RHS, which is a contradiction since they are equal by hx
    nth_rw 4 [facx] at hx; any_goals assumption
  -- We first prove the case when $x.factorization p$ is greater or equal to $2$.
  -- In the case, we prove the last term of the LHS is less than the last term of the RHS by applying aux2
  -- and prove the rest of the terms on RHS is less or equal to the corresponding term on LHS by applying aux1
    by_cases h' : 2 ≤ x.factorization p
    · suffices :(∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1)) * (x.factorization p + p) <
  (∏ q ∈ x.primeFactors \ {p}, q ^ x.factorization q) * p ^ x.factorization p
      · linarith
      apply Nat.mul_lt_mul_of_le_of_lt'; apply Finset.prod_le_prod
      · intros; linarith
      · intro q hq; simp at hq; rcases hq with ⟨⟨qpr,⟨qdvd⟩⟩,pneq⟩
        apply aux1; by_contra h''; simp at h''; rw [Nat.factorization_eq_zero_iff] at h''
        rcases h'' with _|_|_; any_goals contradiction
        apply Nat.Prime.two_le; assumption
      · apply aux2; assumption; linarith
      apply Finset.prod_pos; intros; linarith
  -- In the second case, we first prove that $x.factorization p$ has to be equal to $1$
    replace h' : x.factorization p = 1 := by
      suffices : 0 < x.factorization p; linarith
      by_contra h''; simp at h''; rw [Nat.factorization_eq_zero_iff] at h''
      rcases h'' with _|_|_; any_goals contradiction
    rw [h', pow_one] at hx
  -- Prove that $p$ has to divide one of the factors in the product on LHS
    have : ∃ q ∈ x.primeFactors \ {p}, p ∣ x.factorization q + 1 := by
      suffices : p ∣ ∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1)
      · rw [Prime.dvd_finset_prod_iff] at this; assumption
        exact Nat.prime_iff.mp hp
      suffices : p ∣ (∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1)) * (1 + p)
      · rw [Nat.Prime.dvd_mul] at this; cases this; assumption
        rename_i h''; simp at h''; simp_all; assumption
      rw [hx]; norm_num
  -- Assume this factor corresponds to a prime factor $q$, isolate this factor from the product on both sides of hx
    rcases this with ⟨q, ⟨hq1,hq2⟩⟩
    have : x.primeFactors \ {p} = (x.primeFactors \ {p}) \ {q} ∪ {q} := by
      rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left.mpr]
      rw [Finset.singleton_subset_iff]; assumption
    rw [this, Finset.prod_union, Finset.prod_union] at hx; simp at hx
    rw [mul_assoc, mul_assoc] at hx
  -- Prove that the product of terms corresponding to $p$, $q$ on the LHS of hx is less than that of the RHS by applying aux3
  -- and prove the rest terms on LHS is less or equal to those on RHS by applying aux1
    suffices : (∏ x_1 ∈ (x.primeFactors \ {p}) \ {q}, (x.factorization x_1 + 1)) * ((x.factorization q + 1) * (1 + p)) <
  (∏ x_1 ∈ (x.primeFactors \ {p}) \ {q}, x_1 ^ x.factorization x_1) * (q ^ x.factorization q * p)
    · linarith
    apply Nat.mul_lt_mul_of_le_of_lt'; apply Finset.prod_le_prod
    · intros; linarith
    · intro q hq; simp at hq; rcases hq with ⟨⟨⟨_,⟨⟩⟩,_⟩,_⟩
      apply aux1; by_contra h''; simp at h''; rw [Nat.factorization_eq_zero_iff] at h''
      rcases h'' with _|_|_; any_goals contradiction
      apply Nat.Prime.two_le; assumption
    · apply aux3; apply Nat.le_of_dvd at hq2; assumption
      linarith; simp at hq1; rcases hq1 with ⟨⟨⟩⟩
      apply Nat.Prime.two_le; any_goals assumption
    apply Finset.prod_pos; intros; any_goals linarith
    any_goals apply Finset.sdiff_disjoint
    intro h'; rw [Nat.sub_eq_zero_iff_le] at h'; linarith
    any_goals simp; intro; linarith
    simp; constructor; intro; linarith; push_neg; assumption
-- After proving the key lemma, we apply Set.infinite_of_injOn_mapsTo to it and rewrite our final goal,
-- which is essentially the same as the fact that there are infinitely many prime numbers in natural numbers
  apply Set.infinite_of_injOn_mapsTo _ key;
  have infiprimes:= Nat.infinite_setOf_prime
  have : {p | Nat.Prime p} \ {2,3} ∪ {2,3} = {p | Nat.Prime p} := by rw [Set.diff_union_self]; simp; norm_num
  rw [← this, Set.infinite_union] at infiprimes; simp at infiprimes; assumption
-- Finally prove that the function pS1 is injective on the set of prime numbers
  rw [Set.InjOn]; simp; intro a ha _ _ b hb _ _ hab
  replace ha : 2 ≤ a := by apply Nat.Prime.two_le; assumption
  replace hb : 2 ≤ b := by apply Nat.Prime.two_le; assumption
  simp [pS1] at hab; by_contra h'; push_neg at h'
  rw [Nat.ne_iff_lt_or_gt] at h'; rcases h' with h'|h'
  · have : a ^ (a - 1) < b ^ (a - 1) := by
      rw [Nat.pow_lt_pow_iff_left]; assumption; intro ha
      rw [Nat.sub_eq_zero_iff_le] at ha; linarith
    have : b ^ (a - 1) < b ^ (b - 1) := by
      rw [Nat.pow_lt_pow_iff_right, Nat.sub_lt_sub_iff_right]; assumption
      any_goals linarith
    linarith
  have : b ^ (b - 1) < a ^ (b - 1) := by
    rw [Nat.pow_lt_pow_iff_left]; assumption; intro ha
    rw [Nat.sub_eq_zero_iff_le] at ha; linarith
  have : a ^ (b - 1) < a ^ (a - 1) := by
    rw [Nat.pow_lt_pow_iff_right, Nat.sub_lt_sub_iff_right]; assumption
    any_goals linarith
  linarith
