import Mathlib
open Polynomial

/-
Find all integer-coefficient polynomials $f(x)$ such that for all positive integers $n$, we have
$$
f(n) \mid 2^{n}-1 \text {. }
$$
-/
theorem number_theory_204056 {f : Polynomial ℤ} : (∀ n : ℕ, f.eval (n : ℤ) ∣ (2 ^ n - 1)) ↔  f = C 1 ∨ f = C (-1) := by
  constructor
  intro fn
  -- 假设 $f(x)$ 不为常数,
  by_cases fdegree : 0 < f.degree
  -- 不妨设 $f(x)$ 首项系数为正, 则存在正整数 $N$, 使得当 $x \geqslant N$ 时, $f(x) \geqslant 2$.
  let g := if 0 ≤ f.leadingCoeff then f else -f
  have hglc : 0 ≤ g.leadingCoeff := by
    by_cases h : 0 ≤ f.leadingCoeff
    · simp [g,h]
    simp [g,h] ;linarith
  have hgd : 0 < g.degree := by
    simp [g]
    split ;exact fdegree ;simp ;exact fdegree
  let g' := Polynomial.map (Int.castRingHom ℚ) g
  have h0 : Function.Injective ⇑(Int.castRingHom ℚ) := by
      exact RingHom.injective_int (Int.castRingHom ℚ)
  -- 则存在正整数 $N$, 使得当 $x \geqslant N$ 时, $f(x) \geqslant 2$.
  have h1 : Filter.Tendsto (fun x => eval x g') Filter.atTop Filter.atTop := by
    apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    simp only [g']
    rw [Polynomial.degree_map_eq_of_injective h0]
    exact hgd
    simp only [g']
    rw [Polynomial.leadingCoeff_map' h0]
    simp [hglc]
  apply Filter.tendsto_atTop_atTop.mp at h1
  specialize h1 2
  -- 任取一个正整数 $n, n \geqslant N$,
  rcases h1 with ⟨N,h1'⟩ 
  have h2 : ∃ m : ℕ , N ≤ m := by
    exact exists_nat_ge N
  rcases h2 with ⟨m,h2'⟩
  let n := m + 1
  replace h2' : N ≤ n := by simp [n] ;linarith
  specialize h1' ↑n h2'
  have h3 : 2 ≤ eval ↑n g := by
    qify
    have : eval (↑n) g' = ↑(eval (↑n) g) := by
      simp [g']
    simp [n] at h1' this
    linarith
  have h4 : (eval ↑n g).natAbs ≠ 1 := by
    omega
  -- 取 $f(n)$ 的素因子 $p$, 
  apply Int.exists_prime_and_dvd at h4
  rcases h4 with ⟨p,hp1,hp2⟩
  let p' := abs p 
  -- 由于 $f(n) \mid$ $2^{n}-1$, 所以 $2^{n} \equiv 1(\bmod p)$.
  have h5 : 2 ^ n % p' = 1 := by
    specialize fn n
    have : eval (↑n) g ∣ 2 ^ n - 1 := by
      simp only [g]
      split
      exact fn
      simp [fn]
    have : p' ∣ 2 ^ n - 1 := by
      apply Int.dvd_trans ?_ this
      simp [p',hp2]
    apply exists_eq_mul_left_of_dvd at this
    rcases this with ⟨m,hm⟩
    replace hm : (2:ℤ)^ n = m * p' + 1 := by linarith
    simp [hm,Int.add_emod]
    refine Int.emod_eq_of_lt (by simp) ?_
    have : Prime p' ∧ 0 ≤ p' := by
      simp [p']
      exact Prime.abs hp1
    rcases this with ⟨this1,this2⟩ 
    by_contra!
    interval_cases p' <;> simp at this1
  -- 又由于 $f(n+p) \equiv f(n) \equiv 0(\bmod p), f(n+p) \mid 2^{n+p}-1$,所以 $2^{n+p} \equiv 1(\bmod p)$,
  have h6 : 2 ^ (n+p.natAbs) % p' = 1 := by
    specialize fn (n+p.natAbs)
    have h7 : ↑p.natAbs = p' := by simp
    rw [Nat.cast_add,h7] at fn
    have : eval (↑n + p') g ∣ 2 ^ (n + p.natAbs) - 1 := by
      simp only [g]
      split
      exact fn
      simp [fn]
    have this' : p' ∣ eval (↑n + p') g := by
      have : p' ∣ eval (↑n + p') g - eval (↑n) g := by
        rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
        have : ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * (↑n + p') ^ i =
        ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * ((↑n + p') ^ i - ↑n ^ i) 
        +
        ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i * ↑n ^ i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring_nf
        rw [this]
        simp
        apply Finset.dvd_sum
        intro j hj
        apply dvd_mul_of_dvd_right
        have : Finset.range (j + 1) = insert j (Finset.range j) := by
          exact Finset.range_add_one
        rw [add_pow,this,Finset.sum_insert]
        simp
        apply Finset.dvd_sum
        intro k hk
        apply dvd_mul_of_dvd_left
        apply dvd_mul_of_dvd_right
        refine dvd_pow_self p' ?_
        simp at hk
        omega
        simp
      have this' : p' ∣ eval (↑n) g := by
        simp [p',hp2]
      have := Int.dvd_add this this'
      simp at this
      exact this
    have : p' ∣ 2 ^ (n + p.natAbs) - 1 := by
      apply Int.dvd_trans this' this
    apply exists_eq_mul_left_of_dvd at this
    rcases this with ⟨m,hm⟩
    replace hm : 2 ^ (n + p.natAbs) = m * p' + 1 := by linarith
    simp [hm,Int.add_emod]
    refine Int.emod_eq_of_lt (by simp) ?_
    have : Prime p' ∧ 0 ≤ p' := by
      simp [p']
      exact Prime.abs hp1
    rcases this with ⟨this1,this2⟩ 
    by_contra!
    interval_cases p' <;> simp at this1
  -- 从而 $2^{p} \equiv 1(\bmod p)$.
  have h7 : 2 ^ p.natAbs % p' = 1:= by
    rw [pow_add,Int.mul_emod,h5,one_mul] at h6
    simp at h6
    exact h6
  -- 由费马小定理, $2^{p} \equiv 2(\bmod p)$, 
  have h8 : 2 ^ (p.natAbs - 1) ≡ 1 [ZMOD ↑p.natAbs] := by 
    apply Int.ModEq.pow_card_sub_one_eq_one
    exact Int.prime_iff_natAbs_prime.mp hp1
    apply Int.coprime_iff_nat_coprime.mpr
    simp
    by_contra!
    simp at this
    have this' : ∃ m , 2 ^ n = 1 + p' * m := by
      refine Int.modEq_iff_add_fac.mp ?_
      rw [← h5]
      exact Int.mod_modEq (2 ^ n) p'
    rcases this' with ⟨k,hk⟩
    have : Odd ((2:ℤ) ^ n) := by
      rw [hk]
      refine Int.odd_add.mpr ?_
      simp
      exact Even.mul_right this k
    have this' : ¬ Odd ((2:ℤ) ^ n) := by
      simp
      use (2 ^ m)
      simp [n,pow_add,mul_two]
    exact this' this
  replace h8 : 2 ^ (p.natAbs - 1) * 2 ^ 1 ≡ 1 * 2 ^ 1 [ZMOD ↑p.natAbs] := by
    exact
      Int.ModEq.mul (h0 (congrArg (⇑(Int.castRingHom ℚ)) (h0 (congrArg (⇑(Int.castRingHom ℚ)) h8))))
        (h0 rfl)
  rw [← pow_add, Nat.sub_add_cancel] at h8
  simp at h8
  -- 从而 $1 \equiv 2(\bmod p)$, 矛盾!
  have h9 : 2 ^ p.natAbs % |p| = 2 % |p| := by
    exact h0 (congrArg (⇑(Int.castRingHom ℚ)) (h0 (congrArg (⇑(Int.castRingHom ℚ)) h8)))
  simp only [p'] at h7
  rw [h7] at h9
  by_cases h10 : 2 < |p|
  · have : 2 % |p| = 2 := by refine Int.emod_eq_of_lt (by simp) h10
    simp [this] at h9
  simp at h10
  have h11 : 0 ≤ |p| := by simp
  interval_cases |p| <;> simp at h9
  refine Nat.one_le_iff_ne_zero.mpr ?_
  by_contra!
  simp at this
  simp [this] at hp1
  -- 所以 $f(x)$ 为常数, 设 $f(x)=a$.
  simp at fdegree
  apply Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr at fdegree
  apply Polynomial.natDegree_eq_zero.mp at fdegree
  -- 由于 $f(1) \mid 2^{1}-1$, 即 $a \mid 1$, 知 $a= \pm 1$. 
  rcases fdegree with ⟨x,hx⟩
  simp [← hx] at fn
  specialize fn 1
  simp at fn
  by_cases h : 0 ≤ x
  · have : x = 1 := by
      apply Int.eq_one_of_dvd_one
      linarith ;exact fn
    rw [← hx,this] ;simp
  have : (-x) = 1 := by
    apply Int.eq_one_of_dvd_one
    linarith ;simp [fn]
  rw [← hx,← this];simp
  -- 所以所求整系数多项式为 1或-1.
  intro hc
  rcases hc with hc |hc
  simp [hc]
  simp [hc]
