import Mathlib

/-- How many pairs of positive integers (a,b) with $a+b\le 100$ satisfy the equation

\[\frac{a+b^{-1}}{a^{-1}+b}=13?\]

$\text{(A) } 1\quad \text{(B) } 5\quad \text{(C) } 7\quad \text{(D) } 9\quad \text{(E) } 13$ -/
theorem algebra_97297 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b ≤ 100 ∧
    ((a:ℚ) + 1 / b) / (1 / a + (b:ℚ)) = 13}.ncard = 7 := by

  -- Let $s$ be the set of all pairs of positive integers $(a, b)$ such that $a + b \le 100$ and
  -- $\frac{a + b^{-1}}{a^{-1} + b} = 13$.
  set s := {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b ≤ 100 ∧
    ((a:ℚ) + 1 / b) / (1 / a + (b:ℚ)) = 13}

  -- First, we will simplify the definition of $s$. We claim that for any positive integers $a$ and
  -- $b$, $\frac{a + b^{-1}}{a^{-1} + b} = 13$ iff $a^2 b + a = 13 b + 13 a b^2$.
  have lem1 {a b : ℕ} (ha : a > 0) (hb : b > 0) :
      ((a:ℚ) + 1 / b) / (1 / a + (b:ℚ)) = 13 ↔ a^2 * b + a = 13 * b + 13 * a * b^2 := by
    constructor
    -- For the left to right direction, assume that $\frac{a + b^{-1}}{a^{-1} + b} = 13$. Then,
    -- clearing out the denominators and then rearranging, we get $a^2 b + a = 13 b + 13 a b^2$.
    · intro h
      qify
      field_simp at h
      linarith

    -- Similarly, for the right to left direction, assume that $a^2 b + a = 13 b + 13 a b^2$. Then,
    -- dividing by $ab$ and then simplifying, we get $\frac{a + b^{-1}}{a^{-1} + b} = 13$.
    · intro h
      qify at h
      field_simp
      linarith

  -- Furthermore, we claim that $a^2 b + a = 13 b + 13 a b^2$ iff $a = 13 b$.
  have lem2 {a b : ℕ} (ha : a > 0) (hb : b > 0) :
      a^2 * b + a = 13 * b + 13 * a * b^2 ↔ a = 13 * b := by
    constructor
    -- For the left to right direction, assume that $a^2 b + a = 13 b + 13 a b^2$.
    · intro h
      zify at h ⊢

      -- Then, rearranging, we get $(ab + 1)(a - 13b) = 0$.
      replace h : (a:ℤ)^2 * b + a - (13 * b + 13 * a * b^2) = 0 := by omega
      replace h : ((a:ℤ) * b + 1) * (a - 13 * b) = 0 := by rw [←h]; ring

      -- Left factor is positive, so the right factor must be zero giving us that $a = 13b$.
      simp at h
      rcases h with (h | h) <;> nlinarith

    -- For the right to left direction, just substitute $a = 13b$ into the equation and simplify.
    · rintro rfl
      ring

  -- Now, let $t$ be the set of all pairs of positive integers $(a, b)$ such that $a > 0$, $b > 0$,
  -- $a + b \le 100$, and $a = 13b$.
  let t := {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a + b ≤ 100 ∧ a = 13 * b}

  -- From the above lemmas, we see that $s = t$.
  have : s = t := by
    ext ⟨a, b⟩
    constructor
    · intro h
      simp only [Set.mem_setOf_eq, s, t] at h ⊢
      rw [lem1 h.1 h.2.1, lem2 h.1 h.2.1] at h
      exact h
    · intro h
      simp only [Set.mem_setOf_eq, s, t] at h ⊢
      rw [lem1 h.1 h.2.1, lem2 h.1 h.2.1]
      exact h

  -- So, it suffices to show that $t$ has $7$ elements.
  rw [this]; clear * - t

  -- To that end, we will show that $t$ is in bijection with the set $\{1, 2, 3, 4, 5, 6, 7\}$.
  suffices (Finset.Ioc 0 7).card = 7 from ?_; swap; simp
  rw [←this, ←Set.ncard_coe_Finset]

  symm
  -- Our map $f$ is defined as $b \mapsto (13b, b)$. Let's show that $f$ maps
  -- $\{1, 2, 3, 4, 5, 6, 7\}$ to $t$ bijectively.
  apply Set.ncard_congr (fun b _ ↦ (13 * b, b))

  -- First, let's show that $f$ maps $\{1, 2, 3, 4, 5, 6, 7\}$ to $t$. Let $b$ be an element of
  -- $\{1, 2, 3, 4, 5, 6, 7\}$ i.e., $0 < b \leq 7$.
  · intro b hb
    simp at hb
    -- Then, $13b + b = 14 b \leq 14 * 7 = 98 < 100$, so $(13b, b) \in t$
    refine ⟨?_, ?_, ?_, rfl⟩
    · omega
    · exact hb.1
    · omega

  -- Our map is injective because the operation multiplication by a nonzero integer is injective.
  · intro b b'
    simp

  -- Lastly, we need to show that $f$ is surjective. Let $(a, b)$ be an element of $t$. Then, $a = 13b$
  · rintro ⟨a, b⟩ ⟨ha, hb, hab1, hab2⟩
    simp
    
    -- It is clear that $f (b) = b$ because the inequality $a + b = 14 b \leq 100$ implies $b \leq 7$.
    refine ⟨hab2.symm, hb, ?_⟩
    omega