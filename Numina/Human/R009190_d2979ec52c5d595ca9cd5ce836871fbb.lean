import Mathlib
/- Let $a, b, c$ be integers. Define $f(x)=a x^{2}+b x+c$. Suppose there exist pairwise distinct integers $u, v, w$ such that $f(u)=0, f(v)=0$, and $f(w)=2$. Find the maximum possible value of the discriminant $b^{2}-4 a c$ of $f$. -/
theorem algebra_609391 : IsGreatest {S : ℤ | ∃ a b c : ℤ, S = b ^ 2 - 4 * a * c ∧ ∃ u v w : ℤ, u ≠ v ∧ a * u ^ 2 + b * u + c = 0 ∧ a * v ^ 2 + b * v + c = 0 ∧ a * w ^ 2 + b * w + c = 2} 16:= by
  constructor
  .
    simp
    use (-2), 0, 2
    norm_num
    use 1, (-1)
    norm_num
  .
    simp [upperBounds]
    intro S a b c hS u v huv hu hv w hw
    subst S
    -- Express b in terms of a, u, and v using the fact that both u and v are roots
    have h1 : b = -a * (u + v) := by
      have h1 : (u - v) * (b + a * (u + v)) = 0:= by linarith
      replace huv : u - v ≠ 0:= by exact sub_ne_zero_of_ne huv
      simp [huv] at h1
      linarith
    -- Express c in terms of a, u, and v
    have h2 : c = a * (u * v):= by subst b ; linarith
    subst b c
    clear hu hv
    -- Rewrite the equation f(w) = 2 in terms of differences
    replace hw : a * (w - u) * (w - v) = 2:= by linarith
    ring_nf
    suffices a ^ 2 * ((w - u) - (w - v)) ^ 2 ≤ 16 by linarith
    -- Let p = w-u and q = w-v for simpler notation
    set p:= w - u
    set q:= w - v
    -- Since a*(p*q) = 2, a must divide 2
    replace h2 : a * (p * q) = 2:= by linarith
    have h1 : a ∣ 2 := by exact Dvd.intro (p * q) h2
    replace h1 : ∃ k : ℤ, 2 = a * k := by exact h1
    rcases h1 with ⟨k, hk⟩
    replace hk : |2| = |a * k|:= by rw [hk]
    field_simp at hk
    rw [show |a * k| = |a| * |k| by exact abs_mul a k] at hk
    replace hk : 2 = a.natAbs * k.natAbs:= by
      zify
      exact hk
    -- Since 2 is prime, we analyze the possible values of |a|
    have g1 : Nat.Prime 2:= by norm_num
    -- Show that |a| divides 2
    replace hk : a.natAbs ∣ 2:= by exact Dvd.intro k.natAbs (id (Eq.symm hk))
    -- Therefore |a| must be either 1 or 2
    replace hk : a.natAbs = 1 ∨ a.natAbs = 2:= by exact (Nat.dvd_prime g1).mp hk
    rcases hk with hk | hk
    .
      -- Case 1: When |a| = 1
      zify at hk
      rw [show a ^ 2 = |a| ^ 2 by exact Eq.symm (sq_abs a)]
      rw [hk]
      simp
      -- Using the fact that |a(pq)| = |2|
      replace h2 : |a * (p * q)| = |2|:= by rw [h2]
      field_simp at h2
      rw [abs_mul a (p * q), abs_mul p q] at h2
      rw [hk] at h2
      simp at h2
      -- Therefore |p||q| = 2
      replace h2 : p.natAbs * q.natAbs = 2:= by zify ; exact h2
      -- Since 2 is prime, |p| must divide 2
      have h3 : p.natAbs ∣ 2:= by exact Dvd.intro q.natAbs h2
      -- Therefore |p| must be either 1 or 2
      replace h3 : p.natAbs = 1 ∨ p.natAbs = 2:= by exact (Nat.dvd_prime g1).mp h3
      -- Note that (p + q)² ≥ 0
      have g2 : (p + q) ^ 2 ≥ 0:= by positivity
      -- We want to prove that 2(p² + q²) ≤ 16
      suffices 2 * |p| ^ 2 + 2 * |q| ^ 2 ≤ 16 by rw [show |p| ^ 2 = p ^ 2 by exact sq_abs p] at this ; rw [show |q| ^ 2 = q ^ 2 by exact sq_abs q] at this ; linarith
      rcases h3 with h3 | h3
      .
        -- Subcase: |p| = 1
        rw [h3] at h2
        simp at h2
        zify at h2 h3
        rw [h2, h3]
        norm_num
      .
        -- Subcase: |p| = 2
        rw [h3] at h2
        simp at h2
        zify at h2 h3
        rw [h2, h3]
        norm_num
    .
      -- Case 2: When |a| = 2
      zify at hk
      rw [show a ^ 2 = |a| ^ 2 by exact Eq.symm (sq_abs a)]
      rw [hk]
      simp
      -- Using the fact that |a(pq)| = |2|
      replace h2 : |a * (p * q)| = |2|:= by rw [h2]
      field_simp at h2
      rw [abs_mul a (p * q), abs_mul p q] at h2
      rw [hk] at h2
      simp at h2
      -- Therefore |p||q| = 1
      replace h2 : p.natAbs * q.natAbs = 1:= by zify ; exact h2
      simp at h2
      rcases h2 with ⟨h2, h3⟩
      zify at h2 h3
      -- Note that (p + q)² ≥ 0
      have g2 : (p + q) ^ 2 ≥ 0:= by positivity
      -- We want to prove that 2(p² + q²) ≤ 4
      suffices 2 * |p| ^ 2 + 2 * |q| ^ 2 ≤ 4 by rw [show |p| ^ 2 = p ^ 2 by exact sq_abs p] at this ; rw [show |q| ^ 2 = q ^ 2 by exact sq_abs q] at this ; linarith
      rw [h2, h3]
      norm_num
