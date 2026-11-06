import Mathlib
/- Let $p$ and $q$ be distinct prime numbers, and let $D$ be a positive integer. Assume that $1 < D < p < q$.
Determine the set of positive integers $a$ such that the fraction $\frac{D+pq+a}{D+a}$ is an integer.
Show that this set of solutions for $a$ is $\{p-D, q-D, pq-D\}$. -/
theorem number_theory_641421 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h1 : 1 < D) (h2 : D < p) (h3 : p < q) (hpq : p ≠ q) : {a : ℕ | D + a ∣ D + p * q + a} = {p - D, q - D, p * q - D}:= by
  ext a
  constructor
  .
    -- Forward direction: If (D+a) divides (D+pq+a), then a is in {p-D, q-D, pq-D}
    intro h
    simp at h
    -- Rearrange to show D + pq + a = pq + (D + a)
    rw [show D + p * q + a = p * q + (D + a) by omega] at h
    -- Prove that D + a divides pq
    replace h : D + a ∣ p * q:= by exact Nat.dvd_add_self_right.mp h
    rcases h with ⟨k, hk⟩
    -- Show that p divides (D+a)*k
    have h4 : p ∣ (D + a) * k:= by exact Dvd.intro q hk
    -- By prime property, either p divides D+a or p divides k
    replace h4 : p ∣ D + a ∨ p ∣ k:= by exact (Nat.Prime.dvd_mul hp).mp h4
    rcases h4 with h4 | h4
    .
      -- Case 1: p divides D+a
      rcases h4 with ⟨t, ht⟩
      rw [ht] at hk
      rw [show p * t * k = p * (t * k) by ring] at hk
      -- Prove q = t*k
      replace hk : q = t * k:= by
        have g : p > 0:= by omega
        exact Nat.eq_of_mul_eq_mul_left g hk
      -- Since q is prime, t must be either 1 or q
      replace hk : t ∣ q:= by exact Dvd.intro k (id (Eq.symm hk))
      replace hk : t = 1 ∨ t = q:= by exact (Nat.dvd_prime hq).mp hk
      rcases hk with hk | hk
      .
        -- If t = 1, then a = p-D
        subst t
        simp at ht
        replace ht : a = p - D:= by omega
        subst a
        simp
      .
        -- If t = q, then a = pq-D
        subst t
        replace ht : a = p * q - D:= by omega
        subst a
        simp
    .
      -- Case 2: p divides k
      rcases h4 with ⟨t, ht⟩
      subst k
      rw [show (D + a) * (p * t) = p * ((D + a) * t) by ring] at hk
      -- Prove q = (D+a)*t
      replace hk : q = (D + a) * t:= by
        have g : p > 0:= by omega
        exact Nat.eq_of_mul_eq_mul_left g hk
      -- Since q is prime, D+a must be either 1 or q
      replace hk : D + a ∣ q:= by exact Dvd.intro t (id (Eq.symm hk))
      replace hk : D + a = 1 ∨ D + a = q:= by exact (Nat.dvd_prime hq).mp hk
      rcases hk with hk | hk
      .
        omega
      .
        -- Therefore a = q-D
        replace hk : a = q - D:= by omega
        subst a
        simp
  .
    -- Backward direction: If a is in {p-D, q-D, pq-D}, then (D+a) divides (D+pq+a)
    intro h
    simp at h
    rcases h with h | h | h
    all_goals
      subst a
      simp
    .
      -- Case a = p-D
      rw [show D + (p - D) = p by omega]
      rw [show D + p * q + (p - D) = p * q + p by omega]
      use q + 1
      ring
    .
      -- Case a = q-D
      rw [show D + (q - D) = q by omega]
      rw [show D + p * q + (q - D) = p * q + q by omega]
      use p + 1
      ring
    .
      -- Case a = pq-D
      have h : p * q > D:= by
        have g : q > 1:= by omega
        exact lt_mul_of_lt_of_one_lt' h2 g
      rw [show D + (p * q - D) = p * q by omega]
      rw [show D + p * q + (p * q - D) = p * q + p * q by omega]
      use 2
      ring
