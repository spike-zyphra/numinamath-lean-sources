import Mathlib

set_option autoImplicit false
noncomputable section
open Filter Classical UniqueFactorizationMonoid Polynomial
open scoped Polynomial

/-
Problem: For a nonnegative integer $n$ define $\operatorname{rad}(n)=1$ if $n=0$ or $n=1$, and $\operatorname{rad}(n)=p_{1} p_{2} \cdots p_{k}$ where $p_{1}<p_{2}<\cdots<p_{k}$ are all prime factors of $n$. Find all polynomials $f(x)$ with nonnegative integer coefficients such that $\operatorname{rad}(f(n))$ divides $\operatorname{rad}\left(f\left(n^{r a d(n)}\right)\right)$ for every nonnegative integer $n$.
Solution: We are going to prove that $f(x)=a x^{m}$ for some nonnegative integers $a$ and $m$. If $f(x)$ is the zero polynomial we are done, so assume that $f(x)$ has at least one positive coefficient. In particular $f(1)>0$.  Let $p$ be a prime number. The condition is that $f(n) \equiv 0(\bmod p)$ implies  $$ f\left(n^{\operatorname{rad}(n)}\right) \equiv 0 \quad(\bmod p) $$  Since $\operatorname{rad}\left(n^{\operatorname{rad}(n)^{k}}\right)=\operatorname{rad}(n)$ for all $k$, repeated applications of the preceding implication show that if $p$ divides $f(n)$ then  $$ f\left(n^{\operatorname{rad}(n)^{k}}\right) \equiv 0 \quad(\bmod p) \quad \text { for all } k . $$  The idea is to construct a prime $p$ and a positive integer $n$ such that $p-1$ divides $n$ and $p$ divides $f(n)$. In this case, for $k$ large enough $p-1$ divides $\operatorname{rad}(n)^{k}$. Hence if $(p, n)=1$ then $n^{r a d(n)^{k}} \equiv 1(\bmod p)$ by FERMAT's little theorem, so that  $$ f(1) \equiv f\left(n^{\operatorname{rad}(n)^{k}}\right) \equiv 0 \quad(\bmod p) . $$  Suppose that $f(x)=g(x) x^{m}$ with $g(0) \neq 0$. Let $t$ be a positive integer, $p$ any prime factor of $g(-t)$ and $n=(p-1) t$. So $p-1$ divides $n$ and $f(n)=f((p-1) t) \equiv f(-t) \equiv 0(\bmod p)$, hence either $(p, n)>1$ or $(2)$ holds. If $(p,(p-1) t)>1$ then $p$ divides $t$ and $g(0) \equiv g(-t) \equiv 0(\bmod p)$, meaning that $p$ divides $g(0)$.  In conclusion we proved that each prime factor of $g(-t)$ divides $g(0) f(1) \neq 0$, and thus the set of prime factors of $g(-t)$ when $t$ ranges through the positive integers is finite. This is known to imply that $g(x)$ is a constant polynomial, and so $f(x)=a x^{m}$.
-/
theorem N5 :
    {f : ℕ[X] | ∀ n, radical (f.eval n) ∣ radical (f.eval (n ^ radical n))} =
    Set.range (fun (a, m) => C a * X ^ m) := by
  -- Lemma: `0` is not prime factors of any number
  have zero_not_mem_primeFactors (n : ℕ) : 0 ∉ primeFactors n := by
    rw [primeFactors]
    simp only [Multiset.mem_toFinset]
    exact zero_not_mem_normalizedFactors _
  -- Lemma: radical of every number is not equal to zero
  have radical_ne_zero {n} (hn : n ≠ 0) : radical n ≠ 0 := by
    simp only [ne_eq, hn, not_false_eq_true]
    rw [← ne_eq, radical, ← Finset.prod_val]
    apply Multiset.prod_ne_zero
    simp only [Finset.mem_val]
    apply zero_not_mem_primeFactors
  -- Lemma: `radical n` is a radical number.
  have IsRadical_radical (n : ℕ) : IsRadical (radical n) := by
    simp only [IsRadical, radical, id_eq]
    intro k m hm
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq ne
      simp only [primeFactors, Nat.factors_eq, List.toFinset_coe, List.coe_toFinset,
        Nat.mem_primeFactorsList', ne_eq, Set.mem_setOf_eq] at hp hq
      change IsRelPrime p q
      rwa [← Nat.coprime_iff_isRelPrime, Nat.coprime_primes hp.1 hq.1]
    · intro p hp
      have := Nat.dvd_trans (Finset.dvd_prod_of_mem _ hp) hm
      simp only [primeFactors, Nat.factors_eq, List.toFinset_coe, List.mem_toFinset,
        Nat.mem_primeFactorsList', ne_eq] at hp
      exact Nat.Prime.dvd_of_dvd_pow hp.1 this
  -- The two definitions of prime factors are equal.
  have primeFactors_eq (n : ℕ) : primeFactors n = n.primeFactors := by
    simp only [primeFactors, Nat.factors_eq, List.toFinset_coe]
    unfold Nat.primeFactors
    congr!
  -- `⊔` is equal to `max`.
  have Nat.sup_eq_max (a b : ℕ) : a ⊔ b = max a b := rfl
  -- The sum of order of `p` in `q`, over `q` in all prime factors of `n`, is 1 iff `p` divides `n`, and 0 otherwise.
  have Nat.sum_primeFactors {p n : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) :
      ∑ q ∈ n.primeFactors, q.factorization p = if p ∣ n then 1 else 0 := calc
    _ = ∑ q ∈ n.primeFactors, if q = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs with hq'
      · simpa [hq'] using Nat.Prime.factorization_self hp
      · apply Nat.factorization_eq_zero_of_not_dvd
        simp only [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)]
        exact (fun h => hq' h.symm)
    _ = _ := by simp [hp, hn]
  -- A lemma that says the radical of multiplication of two numbers are equal to `lcm` of radicals of them.
  have radical_mul_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
      radical (a * b) = (radical a).lcm (radical b) := by
    apply Nat.eq_of_factorization_eq
    · apply radical_ne_zero
      simpa using And.intro ha hb
    · exact Nat.lcm_ne_zero (radical_ne_zero ha) (radical_ne_zero hb)
    · intro p
      rw [Nat.factorization_lcm (radical_ne_zero ha) (radical_ne_zero hb)]
      simp only [radical, id_eq, Finsupp.sup_apply]
      rw [Nat.factorization_prod (by simpa using zero_not_mem_primeFactors _),
        Nat.factorization_prod (by simpa using zero_not_mem_primeFactors _),
        Nat.factorization_prod (by simpa using zero_not_mem_primeFactors _)]
      simp only [primeFactors_eq, Finsupp.finset_sum_apply, Nat.sup_eq_max]
      by_cases hp : p.Prime
      · rw [Nat.sum_primeFactors (mul_ne_zero_iff.mpr (And.intro ha hb)) hp,
          Nat.sum_primeFactors ha hp, Nat.sum_primeFactors hb hp]
        by_cases p_dvd_a : ¬p ∣ a
        · by_cases p_dvd_b : ¬p ∣ b
          · simpa [p_dvd_a, p_dvd_b] using hp.not_dvd_mul p_dvd_a p_dvd_b
          · simp only [Decidable.not_not] at p_dvd_b
            simpa [p_dvd_a, p_dvd_b] using dvd_mul_of_dvd_right p_dvd_b _
        · simp only [Decidable.not_not] at p_dvd_a
          by_cases p_dvd_b : p ∣ b <;>
            simpa [p_dvd_a, p_dvd_b] using dvd_mul_of_dvd_left p_dvd_a _
      · simp [hp]
  -- `p` divides `radical n` iff `p` divides `n`.
  have prime_dvd_radical {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ∣ radical n ↔ p ∣ n := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact dvd_trans h (radical_dvd_self _)
    · simp only [radical, primeFactors_eq, id_eq]
      apply Finset.dvd_prod_of_mem
      simpa using ⟨hp, h, hn⟩
  -- If `y` is squarefree, divides `x` and `x` divides `y ^ n` for some `n`, we can prove `y` is exactly the radical of `x`.
  have eq_radical {x y n : ℕ} (nz : x ≠ 0) (sqf : Squarefree y)
      (dvd : y ∣ x) (dvd_pow : x ∣ y ^ n) : y = radical x := by
    have y_nz : y ≠ 0 := fun hy => by
      rw [hy, Nat.zero_dvd] at dvd
      exact nz dvd
    apply Nat.eq_of_perm_primeFactorsList
    · exact y_nz
    · exact radical_ne_zero nz
    · rw [List.perm_ext_iff_of_nodup]
      · simp only [Nat.mem_primeFactorsList', ne_eq, y_nz, not_false_eq_true, and_true,
          radical_ne_zero nz, and_congr_right_iff]
        refine fun p hp => ⟨fun dvd' => ?_, fun dvd' => ?_⟩
        · exact (prime_dvd_radical hp nz).mpr (Nat.dvd_trans dvd' dvd)
        · exact Nat.Prime.dvd_of_dvd_pow hp <|
            Nat.dvd_trans (Nat.dvd_trans dvd' (radical_dvd_self _)) dvd_pow
      · exact Squarefree.nodup_primeFactorsList sqf
      · exact Squarefree.nodup_primeFactorsList <|
          IsRadical.squarefree (radical_ne_zero nz) (IsRadical_radical x)
  -- For any natural numbers `a` and `b`, if `b ≠ 0` and `a` divides `b`, then `a` divides `radical b ^ n` for some `n`. This is proved using `exists_squarefree_dvd_pow_of_ne_zero`, and the fact that the extracted "squarefree factor" is just the radical, as stated in the lemma `eq_radical`.
  have dvd_radical {a b : ℕ} (nz : b ≠ 0) (dvd : a ∣ b) : ∃ n, a ∣ radical b ^ n := by
    obtain ⟨r, n, h₁, h₂, h₃⟩ := exists_squarefree_dvd_pow_of_ne_zero nz
    rw [eq_radical nz h₁ h₂ h₃] at h₃
    exact ⟨n, Nat.dvd_trans dvd h₃⟩
  -- If `P` is not zero, `P(x) ≠ 0` for sufficiently small `x`.
  have eventually_no_roots {P : ℤ[X]} (hP : P ≠ 0) : ∃ n, ∀ x ≤ n, ¬P.IsRoot x := by
    rw [← Filter.eventually_atBot]
    have := (finite_setOf_isRoot hP).compl_mem_cofinite
    rw [Int.cofinite_eq] at this
    exact (show atBot ≤ atBot ⊔ atTop by apply le_sup_left) this
  -- Proposition for a polynomial is not constant.
  let not_constant (f : ℤ[X]) := ∀ a, f ≠ C a
  -- `no_root_start P` is an integer value, such that every integer less or equal than it can't be the root of `P`.
  let no_root_start {P : ℤ[X]} (hP : P ≠ 0) := (eventually_no_roots hP).choose
  -- Properties for `no_root_start`.
  let le_no_root_start {P : ℤ[X]} (hP : P ≠ 0) : ∀ x ≤ no_root_start hP, P.eval x ≠ 0 :=
    (eventually_no_roots hP).choose_spec
  -- An auxiliary polynomial definition. This will be used in constructing values of `t` such that `p(-t)` has many distinct prime factors.
  let f_aux (f : ℤ[X]) := f.comp (X - f ^ 2) - f
  -- `f_aux` is nonzero if `f` is non-constant. This can be proved by computing the degree of `f_aux`.
  have nonzero_f_aux {f : ℤ[X]} (hf : not_constant f) : f_aux f ≠ 0 := by
    simp only [f_aux]
    suffices (f.comp (X - f ^ 2) - f).natDegree ≠ 0 by
      refine fun h => this (h ▸ Polynomial.natDegree_zero)
    have deg_f : f.natDegree ≠ 0 := by
      simp only [ne_eq, natDegree_eq_zero, eq_intCast, not_exists]
      exact fun x => (hf x).symm
    have deg_X_min_f_sq : 1 < (X - f ^ 2).natDegree := by
      rw [natDegree_sub_eq_right_of_natDegree_lt] <;> (simp; omega)
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp only [natDegree_comp, ne_eq, mul_eq_zero, deg_f, false_or]
      omega
    · simp [natDegree_comp]
      rw [Nat.lt_mul_iff_one_lt_right]
      · assumption
      · omega
  -- If `f` is not constant, then `f - a` is not zero.
  have nonzero_minus {f : ℤ[X]} (hf : not_constant f) (a : ℤ) : f - a ≠ 0 := by
    apply_fun natDegree
    have h : f.natDegree ≠ 0 := by
      simpa [natDegree_zero, natDegree_eq_zero] using fun x => (hf x).symm
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> (simp; try omega)
  -- Definition of the auxiliary function `φ`.
  let φ {f : ℤ[X]} (hf : not_constant f) : ℕ → ℤ :=
    Nat.rec (min (-1) <| min
        ((Finset.Icc (-2) 2 |>.image fun x => no_root_start (nonzero_minus hf x))
          |>.min.untop (by simp))
        (no_root_start (nonzero_f_aux hf)))
      (fun n r => r - f.eval r ^ 2)
  -- `card_φ` is the number of prime factors of `φ hf n`.
  let card_φ {f : ℤ[X]} (hf : not_constant f) (n : ℕ) : ℕ :=
    (f.eval (φ hf n)) |>.natAbs.primeFactors.card
  -- `φ hf n` is less or equal than `no_root_start` of `f_aux`, by definition.
  have φ_le_no_root_start {f : ℤ[X]} (hf : not_constant f) (n : ℕ) :
      φ hf n ≤ no_root_start (nonzero_f_aux hf) := by
    induction n with
    | zero => simp [φ]
    | succ n hn => simp [φ]; nlinarith
  -- `φ hf n` is less or equal than `-1`, by definition.
  have φ_le_neg_1 {f : ℤ[X]} (hf : not_constant f) (n : ℕ) : φ hf n ≤ -1 := by
    induction n with
    | zero => simp [φ]
    | succ n hn => simp [φ]; nlinarith
  -- `φ hf n` is less or equal than the `no_root_start` of `f - x`, where `|x| ≤ 2`.
  have φ_le_no_root_start' {f : ℤ[X]} (hf : not_constant f) (n : ℕ) {x : ℤ}
      (hx : x.natAbs ≤ 2) : φ hf n ≤ no_root_start (nonzero_minus hf x) := by
    induction n with
    | zero =>
      simp only [φ]
      apply min_le_of_right_le
      apply min_le_of_left_le
      rw [← WithTop.coe_le_coe, WithTop.coe_untop]
      apply Finset.min_le
      simp only [Int.reduceNeg, Finset.mem_image, Finset.mem_Icc]
      refine ⟨x, by omega, rfl⟩
    | succ n hn => simp [φ]; nlinarith
  -- Prove that there exists one more prime factor of `f(φ hf (n + 1))` than `f(φ hf n)`. So by induction, we can get `f(φ hf n)` has at least `n` prime factors.
  have card_φ_induction {f : ℤ[X]} (hf : not_constant f) (n : ℕ) :
      card_φ hf n + 1 ≤ card_φ hf (n + 1) := by
    simp only [card_φ, φ]
    set x := φ hf n
    obtain ⟨m, hm⟩ : f.eval x ^ 2 ∣ f.eval (x - f.eval x ^ 2) - f.eval x := by
      refine Int.dvd_trans ?_ (f.sub_dvd_eval_sub _ _)
      ring_nf
      simp
    set a := f.eval x
    -- Prove `m ≠ 0`, since `f_aux(x) ≠ 0`.
    have m_nz : m ≠ 0 := fun zero => by
      simp only [zero, mul_zero] at hm
      have : (f_aux f).eval x = 0 := by simpa [f_aux]
      refine (le_no_root_start (nonzero_f_aux hf) _ (φ_le_no_root_start hf n)) this
    -- Prove `|a| > 2`, since `f(x)` is not equal to -2, -1, 0, 1, 2.
    have abs_a_gt_2 : 2 < a.natAbs := by
      by_contra ha
      simp only [not_lt] at ha
      have : eval x (f - a) ≠ 0 :=
        le_no_root_start (nonzero_minus hf _) _ (φ_le_no_root_start' hf n ha)
      simp at this
    rw [sub_eq_iff_eq_add'] at hm
    rw [hm]
    rw [show a + a ^ 2 * m = a * (1 + a * m) by ring] at hm ⊢
    -- We can prove that `|1 + am| > 1` from `m ≠ 0` and `|a| > 2`.
    have lemma_1 : 1 < (1 + a * m).natAbs := calc
      _ < (a * m).natAbs - Int.natAbs 1 := by
        simp [Int.natAbs_mul]
        rw [← Int.natAbs_ne_zero] at m_nz
        have : 1 ≤ m.natAbs := by omega
        have : 2 * 1 < a.natAbs * m.natAbs := by
          apply Nat.mul_lt_mul_of_lt_of_le <;> assumption
        omega
      _ <= _ := by
        apply Nat.sub_le_of_le_add
        nth_rw 1 [show a * m = 1 + a * m - 1 by simp]
        apply Int.natAbs_sub_le
    rw [Int.natAbs_mul, Nat.primeFactors_mul, Finset.card_union_of_disjoint]
    -- `|1 + am| ≥ 2` and coprime to `f (φ hf n)`, so `1 + am` added one more prime factor at the base of `f (φ hf n)`.
    · simpa only [add_le_add_iff_left, Finset.one_le_card,
        Nat.nonempty_primeFactors, gt_iff_lt] using lemma_1
    · apply Nat.Coprime.disjoint_primeFactors
      rw [← Int.coprime_iff_nat_coprime]
      apply IsCoprime.add_mul_left_right
      apply isCoprime_one_right
    · omega
    · omega
  -- There are at least `n` different prime factors of `φ hf n`.
  have card_φ_ge_n {f : ℤ[X]} (hf : not_constant f) (n : ℕ) : n ≤ card_φ hf n := by
    induction n with
    | zero => simp
    | succ n hn =>
      have := card_φ_induction hf n
      omega
  -- If all prime factors of `f(-1)`, `f(-2)`, ... are in a finite subset `S`, then `f` is constant polynomial.
  -- Here, we use the prime factor set of `N` to replace the finite subset `S`.
  have constant_from_finite_prime_divisors {f : ℤ[X]} {N : ℤ} (hN : N ≠ 0)
      (h : ∀ {p t : ℕ}, Nat.Prime p → 0 < t → (p : ℤ) ∣ eval (-t : ℤ) f → (p : ℤ) ∣ N) :
      ∃ a, f = C a := by
    by_contra hf
    simp only [not_exists] at hf
    let n := N.natAbs.primeFactors.card + 1
    suffices n < n by simp at this
    calc
      _ ≤ _ := card_φ_ge_n hf n
      _ < _ := by
        simp only [card_φ, Nat.lt_add_one_iff]
        gcongr
        intro p hp
        simp only [Nat.mem_primeFactors, ← Int.ofNat_dvd_left,
          ne_eq, Int.natAbs_eq_zero] at hp ⊢
        refine ⟨hp.1, ?_, hN⟩
        have : φ hf n ≤ -1 := φ_le_neg_1 hf n
        apply h hp.1 (show 0 < (φ hf n).natAbs by simp; omega)
        rw [Int.ofNat_natAbs_of_nonpos (by omega)]
        simpa using hp.2.1
  ext f
  constructor
  -- Prove one direction, if `f` satisfies the condition given in the problem, then `f` is equal to `a * x ^ m` for some `a` and `m`.
  · simp only [Set.mem_setOf_eq, eq_natCast, Set.mem_range, Prod.exists]
    intro hf
    by_cases f_nz : f ≠ 0
    -- The difficult case: `f ≠ 0`.
    · -- The multiplicity of `f` is finite.
      have mul_fin : multiplicity.Finite X f := by
        apply Polynomial.multiplicity_finite_of_degree_pos_of_monic
        · simp
        · simp
        · assumption
      let m := multiplicity X f
      obtain ⟨g, hg, g_nz⟩ : ∃ g, f = X ^ m * g ∧ g.eval 0 ≠ 0 := by
        simp only [ne_eq, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff]
        convert multiplicity.Finite.exists_eq_pow_mul_and_not_dvd mul_fin
      let f' := f.map Int.ofNatHom
      let g' := g.map Int.ofNatHom
      have hg' : f' = g' * X ^ m := by rw [mul_comm] at hg; simp [f', g', hg]
      -- f(n) ≠ 0 for any n ≠ 0. Since all coefficients are non-negative and f ≠ 0, there exists one positive coefficient.
      have f_eval_nz {n} (hn : n ≠ 0) : f.eval n ≠ 0 := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
        obtain ⟨k, hk⟩ : ∃ k, f.coeff k ≠ 0 := by
          contrapose f_nz
          simp only [ne_eq, not_exists, Decidable.not_not] at f_nz ⊢
          ext k
          apply f_nz
        simpa using ⟨k, hk, by simp [hn]⟩
      -- Lemma 1: If `p` divides `f(n)`, then `p` divides `f(n ^ (rad(n) ^ k))`.
      have lemma_1 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) (dvd : p ∣ f.eval n) :
          p ∣ f.eval (n ^ (radical n ^ k)) := by
        induction k with
        | zero => simpa using dvd
        | succ k hk =>
          rw [← prime_dvd_radical hp <| f_eval_nz (by simp [hn])] at hk ⊢
          apply Nat.dvd_trans hk
          convert hf (n ^ (radical n ^ k)) using 3
          rw [radical_pow _ <| Nat.pos_pow_of_pos _ <|
            Nat.pos_of_ne_zero <| radical_ne_zero hn, ← pow_mul, pow_succ]
      let N := g'.eval 0 * f'.eval 1
      have lemma_2 {p t : ℕ} (hp : p.Prime) (ht : 0 < t)
          (dvd : (p : ℤ) ∣ g'.eval (-t : ℤ)) : (p : ℤ) ∣ N := by
        by_cases dvd_t: p ∣ t
        -- If $(p,(p-1) t)>1$ then $p$ divides $t$ and $g(0) \equiv g(-t) \equiv 0(\bmod p)$, meaning that $p$ divides $g(0)$.
        · have : (p : ℤ) ∣ g'.eval 0 - g'.eval (-t : ℤ) := by
            apply Int.dvd_trans
              (show (p : ℤ) ∣ (0 - (-t) : ℤ) by simp [dvd_t, Int.natCast_dvd_natCast])
            apply Polynomial.sub_dvd_eval_sub
          rw [← Int.natCast_dvd_natCast] at dvd_t
          rw [dvd_sub_left dvd] at this
          apply dvd_mul_of_dvd_left this
        -- If $p$ not divides $t$, then $(p, n) = 1$, and $n^{rad(n)^{k}} \equiv 1(\bmod p)$ by Fermat's little theorem, so we have $f(1) \equiv f\left(n^{\operatorname{rad}(n)^{k}}\right) \equiv 0 \quad(\bmod p)$. Then $p$ divides $f(1)$.
        · suffices (p : ℤ) ∣ f'.eval 1 by apply dvd_mul_of_dvd_right this
          let n := (p - 1) * t
          have n_nz : n ≠ 0 := by
            simp only [ne_eq, mul_eq_zero, not_or, n]
            have := hp.one_lt
            exact ⟨by omega, by omega⟩
          obtain ⟨k, hk⟩ : ∃ k, p - 1 ∣ radical n ^ k := dvd_radical n_nz (Nat.dvd_mul_right _ _)
          rw [← dvd_sub_right (b := f'.eval (n ^ radical n ^ k : ℤ))]
          -- p divides $f(n^{rad(n)^k}) - f(1)$, using `Polynomial.sub_dvd_eval_sub` and Fermat's little theorem, `Int.ModEq.pow_card_sub_one_eq_one`.
          · suffices (p : ℤ) ∣ (n ^ radical n ^ k - 1 : ℤ) from
              Int.dvd_trans this (f'.sub_dvd_eval_sub _ _)
            rw [← Int.modEq_iff_dvd, Int.modEq_comm]
            obtain ⟨l, hl⟩ := hk
            rw [hl, pow_mul, show (1 : ℤ) = 1 ^ l by simp]
            apply Int.ModEq.pow
            apply Int.ModEq.pow_card_sub_one_eq_one hp
            apply Nat.Coprime.isCoprime
            apply Nat.Coprime.mul
            · have := hp.one_lt
              nth_rw 2 [show p = p - 1 + 1 by omega]
              simp [Nat.coprime_self_add_right]
            · rwa [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          -- p divides $f(n^{rad(n)^k})$.
          · simp only [f']
            norm_cast
            rw [Polynomial.eval_natCast_map]
            simp only [Polynomial.eval_natCast_map, Nat.cast_pow, Nat.cast_id, eq_natCast]
            norm_cast
            apply lemma_1 hp n_nz
            zify
            rw [show f.eval n = f'.eval (n : ℤ) by simp [f', Polynomial.eval_natCast_map]]
            rw [← dvd_sub_right <| Int.dvd_trans dvd <| Polynomial.eval_dvd ⟨_, hg'⟩]
            refine Int.dvd_trans ?_ (Polynomial.sub_dvd_eval_sub _ _ _)
            simp only [n, Nat.cast_mul, Int.natCast_sub hp.one_le]
            ring_nf
            simp
      have N_nz : N ≠ 0 := by simpa [N, f', g'] using ⟨g_nz, f_eval_nz (by norm_num)⟩
      obtain ⟨a, ha⟩ := constant_from_finite_prime_divisors N_nz lemma_2
      use a.natAbs, m
      simp only [ha, eq_intCast, f'] at hg'
      apply Polynomial.map_injective Int.ofNatHom (by simp [Int.ofNatHom, Function.Injective])
      rw [hg']
      apply_fun (coeff · m) at hg'
      suffices ((a.natAbs : ℤ) : ℤ[X]) = (a : ℤ[X]) by rw [Int.cast_natCast] at this; simpa
      simp at hg' ⊢
      simp [←hg']
    -- The easy case: if `f = 0`, then `f = 0 * x ^ 0`.
    · simp only [ne_eq, Decidable.not_not] at f_nz
      use 0, 0
      simp [f_nz]
  -- Prove the reverse direction: if `f = a * x ^ m`, then `f` satisfy the condition in the problem.
  · simp only [eq_natCast, Set.mem_range, Prod.exists, Set.mem_setOf_eq, forall_exists_index]
    intro a m hf n
    simp only [← hf, eval_mul, eval_natCast, Nat.cast_id, eval_pow, eval_X]
    -- Some special cases: a = 0, n = 0 and m = 0.
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hn : n = 0
      · simp [hn]
      · rw [← pow_mul,
          radical_mul_lcm ha (by simp [hn]), radical_mul_lcm ha (by simp [hn])]
        apply lcm_dvd_lcm (by simp)
        by_cases hm : m = 0
        · simp [hm]
        · rw [radical_pow _ (by omega), radical_pow _ _]
          apply mul_pos
          · have : radical n ≠ 0 := by exact radical_ne_zero hn
            omega
          · omega
