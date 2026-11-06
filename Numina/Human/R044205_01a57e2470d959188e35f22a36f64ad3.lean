import Mathlib

/- Let $\mathbb{P}$ be the set of all prime numbers. Find all functions $f: \mathbb{P} \rightarrow \mathbb{P}$ such that

$$
f(p)^{f(q)}+q^{p}=f(q)^{f(p)}+p^{q}
$$

holds for all $p, q \in \mathbb{P}$. -/
theorem number_theory_605960 (f : ℕ → ℕ) (hf : ∀ p, p.Prime → (f p).Prime) :
  (∀ p q, p.Prime → q.Prime → f p ^ f q + q ^ p = f q ^ f p + p ^ q) ↔
  ∀ p, p.Prime → f p = p := by
  -- Obviously, the identical function $f(p)=p$ for all $p \in \mathbb{P}$ is a solution.
  -- We will show that this is the only one.
  constructor
  intro hpq
  -- First we will show that $f(2)=2$.
  -- Taking $q=2$ and $p$ any odd prime number, we have
  -- $$ f(p)^{f(2)}+2^{p}=f(2)^{f(p)}+p^{2} . $$
  have h1 : ∀ (d : ℕ),  ((Nat.Prime d) → ((f d) ^ (f (2 : ℕ)) + 2 ^ d = (f (2 : ℕ)) ^ (f d) + d ^ 2)) := by
    intro p hp
    apply hpq
    exact hp ;exact Nat.prime_two
  -- Assume that $f(2) \neq 2$.
  -- It follows that $f(2)$ is odd and so $f(p)=2$ for any odd prime number $p$.
  by_cases h2 : f 2 ≠ 2
  have h3 : Odd (f 2) := by
    have : (f 2).Prime := hf 2 Nat.prime_two
    exact Nat.Prime.odd_of_ne_two this h2
  have h4 : ∀ p, p.Prime → p ≠ 2 → f p = 2 := by
    intro p hp hp2
    specialize h1 p hp
    have : Odd p := Nat.Prime.odd_of_ne_two hp hp2
    have : Odd (p ^ 2) := Odd.pow this
    have this' : Odd (f 2 ^ f p) := Odd.pow h3
    have : Even (f 2 ^ f p + p ^ 2) := by
      apply Nat.even_add'.mpr ;simp [this', this]
    rw [← h1] at this
    apply Nat.even_add.mp at this
    have : Even (f p ^ f 2) := by
      apply this.mpr ;refine Nat.even_pow.mpr (by simp ;exact Nat.Prime.ne_zero hp)
    apply (Nat.even_pow' (Nat.Prime.ne_zero (hf 2 Nat.prime_two))).mp at this
    have this' : (f p).Prime := hf p hp
    exact (Nat.Prime.even_iff (hf p hp)).mp this
  -- Taking any two different odd prime numbers $p, q$ we have
  -- $$ 2^{2}+q^{p}=2^{2}+p^{q} \Rightarrow p^{q}=q^{p} \Rightarrow p=q, $$
  -- contradiction.
  specialize hpq 3 5 ;simp [Nat.prime_three,Nat.prime_five] at hpq
  have h35 : f 3 = 2 ∧ f 5 = 2 := by
    constructor ;apply h4 ;exact Nat.prime_three ;simp
    apply h4 ;exact Nat.prime_five ;simp
  simp [h35] at hpq
  --  Hence, $f(2)=2$.
  simp at h2
  -- So for any odd prime number $p$ we have
  -- $$ f(p)^{2}+2^{p}=2^{f(p)}+p^{2} . $$
  rw [h2] at h1
  -- Copy this relation as $$ 2^{p}-p^{2}=2^{f(p)}-f(p)^{2} $$
  have h3 : ∀ p ,p.Prime → (2 : ℤ) ^ p - p ^ 2 = 2 ^ f p - f p ^ 2 := by
    intro p hp
    specialize h1 p hp ;rw [add_comm] at h1
    apply tsub_eq_tsub_of_add_eq_add
    nth_rewrite 1 [← Nat.cast_two,← Nat.cast_pow,← Nat.cast_pow,← Nat.cast_add,h1]
    simp
  -- Let $T$ be the set of all positive integers greater than 2, i.e. $T=\{3,4,5, \ldots\}$.
  -- The function $g: T \rightarrow \mathbb{Z}, g(n)=2^{n}-n^{2}$, is strictly increasing, i.e.
  let g (n : ℕ) : ℤ := 2 ^ (n + 3) - (n + 3) ^ 2
  have h4 : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    -- $$ g(n+1)-g(n)=2^{n}-2 n-1&gt;0 $$
    -- for all $n \in T$.
    intro n ;simp only [g,Nat.cast_add] ;apply sub_neg.mp ;ring_nf
    -- We show this by induction.
    induction n with
    -- Indeed, for $n=3$ it is true, $2^{3}-2 \cdot 3-1&gt;0$.
    | zero => simp
    -- Assume that $2^{k}-2 k-1&gt;0$. It follows that for $n=k+1$ we have
    -- $$ 2^{k+1}-2(k+1)-1=\left(2^{k}-2 k-1\right)+\left(2^{k}-2\right)&gt;0 $$
    -- for any $k \geq 3$. Therefore, (2) is true for all $n \in T$.
    | succ k ih =>
      have : (7 : ℤ) + (↑(k + 1) * 2 - 2 ^ (k + 1) * 8) < 7 + (↑k * 2 - 2 ^ k * 8) := by
        apply sub_neg.mp ;rw [Nat.cast_add];ring_nf
        apply sub_neg.mpr
        have : (1 : ℝ) * 8 ≤ 2 ^ k * 8 := by
          apply (mul_le_mul_right (by simp)).mpr
          refine one_le_pow₀ (by simp)
        linarith
      linarith
  -- As a consequence, (1) holds if and only if $f(p)=p$ for all odd prime numbers $p$, as well as for $p=2$.
  -- Therefore, the only function that satisfies the given relation is $f(p)=p$, for all $p \in \mathbb{P}$.
  intro p hp
  by_cases hp2 : p = 2
  simp [hp2,h2]
  have hp3 : 3 ≤ p := by
    refine Nat.succ_le_of_lt ?_
    refine Nat.two_lt_of_ne ?_ ?_ hp2
    exact Nat.Prime.ne_zero hp
    exact Nat.Prime.ne_one hp
  specialize h3 p hp
  have h5 : g (p - 3) = 2 ^ p - p ^ 2 := by
    simp only [g] ;rw [Nat.cast_sub,Nat.sub_add_cancel hp3] ;ring_nf ;exact hp3
  have h6 : Function.Injective g := by exact StrictMono.injective h4
  have hfp3 : 3 ≤ f p := by
    have : (f p).Prime := hf p hp
    refine Nat.succ_le_of_lt ?_
    refine Nat.two_lt_of_ne ?_ ?_ ?_
    exact Nat.Prime.ne_zero (hf p hp)
    exact Nat.Prime.ne_one (hf p hp)
    by_contra!
    simp [this] at h3
    have : g 1 = 0 := by simp [g]
    rw [← h5] at h3
    have : g (p-3) = g 1 := by linarith
    have : p - 3 = 1 := by exact h6 h3
    have : p = 1 + 3 := by exact (Nat.sub_eq_iff_eq_add hp3).mp (h6 h3)
    norm_num at this
    rw [this] at hp ;norm_num at hp
  have h7 : g (f p - 3) = g (p - 3) := by
    rw [h5,h3] ;simp [g] ;rw [Nat.cast_sub,Nat.sub_add_cancel hfp3] ;ring_nf ;exact hfp3
  have h8 : f p - 3 = p - 3 := by exact h6 h7
  have : f p = f p - 3 + 3 := by
    exact (Nat.sub_eq_iff_eq_add hfp3).mp (h6 rfl)
  rw [this,h8] ;exact Nat.sub_add_cancel hp3
  intro hprime p q hp hq
  simp [hprime p hp,hprime q hq,add_comm]