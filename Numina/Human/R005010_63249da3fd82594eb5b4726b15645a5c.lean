import Mathlib

/- Let $f$ be a real-valued function defined on the positive integers satisfying the following condition: For all $n>1$ there exists a prime divisor $p$ of $n$ such that

$$
f(n)=f\left(\frac{n}{p}\right)-f(p)
$$

Given that $f(2001)=1$, what is the value of $f(2002)$ ? -/
theorem number_theory_605042 (f : ℕ → ℝ)
  (h : ∀ n > 1, ∃ p, Nat.Prime p ∧ p ∣ n ∧ f n = f (n / p) - f p)
  (hf : f 2001 = 1) : f 2002 = 2 := by

  -- We show that $f(p) = f(1)/2$ for if $p$ is a prime.
  have h1p : ∀ p, Nat.Prime p → f p = f 1 / 2 := by
    intro p hp
    obtain ⟨q, ⟨hqp, hqdvd, hqf ⟩ ⟩ := h p (by norm_num; linarith [Nat.Prime.one_lt hp])
    have : q = p := by exact (Nat.prime_dvd_prime_iff_eq hqp hp).mp hqdvd
    rw [this] at hqf
    clear this
    have : p / p = 1 := by apply Nat.div_self; exact Nat.Prime.pos hp
    rw [this] at hqf
    clear this
    field_simp
    replace hqf := congrArg (fun t => t + f p) hqf
    simp at hqf
    rw [mul_two]
    exact hqf

  -- We show that $f(pq) = 0$ for if $p$ and $q$ are primes.
  have h2p : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → f (p * q) = 0 := by
    intro p q hp hq
    have t1 : p > 1 := by exact Nat.Prime.one_lt hp
    have t2 : q > 1 := by exact Nat.Prime.one_lt hq
    have : p * q > 1 := by exact Right.one_lt_mul' t1 t2
    obtain ⟨ r, ⟨ hrp, hrdvd, hrf ⟩ ⟩ := h (p * q) this
    have : r = p ∨ r = q := by
      rw [Nat.Prime.dvd_mul hrp] at hrdvd
      repeat rw [Nat.prime_dvd_prime_iff_eq hrp] at hrdvd
      . exact hrdvd
      . exact hq
      . exact hp

    rcases this with g | g
    repeat
      rw [hrf]; rw [g]; field_simp; simp [h1p q hq, h1p p hp]

  -- We show that $f(pqr) = -f(1)/2$ for if $p$, $q$, $r$ are primes.
  have h3p : ∀ p q r: ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → f (p * q * r) =  -f 1 / 2 := by
    intro p q r hp hq hr
    have t1 : p > 1 := by exact Nat.Prime.one_lt hp
    have t2 : q > 1 := by exact Nat.Prime.one_lt hq
    have t3 : r > 1 := by exact Nat.Prime.one_lt hr
    have : p * q * r > 1 := by
      have : p * q > 1 := by exact Right.one_lt_mul' t1 t2
      exact Right.one_lt_mul' this t3
    obtain ⟨ s, ⟨ hsp, hsdvd, hsf ⟩ ⟩ := h (p * q * r) this
    rw [hsf]
    have : (s = p ∨ s = q) ∨ s = r := by
      repeat rw [Nat.Prime.dvd_mul hsp] at hsdvd
      repeat rw [Nat.prime_dvd_prime_iff_eq hsp] at hsdvd
      . exact hsdvd
      . exact hr
      . exact hq
      . exact hp

    rcases this with g | g
    . rcases g with g' | g'
      . rw [g']
        have : p * q * r / p = q * r := by
          calc
            _ = r * q * p / p := by ring_nf
            _ = _  := by field_simp; ring
        rw [this]; clear this
        simp [h2p q r hq hr, h1p r hr, h1p p hp]; ring
      . rw [g']
        have : p * q * r / q = p * r := by
          calc
            _ = p * r * q / q := by ring_nf
            _ = _  := by field_simp
        rw [this]; clear this
        simp [h2p p r hp hr, h1p r hr, h1p q hq]; ring
    . rw [g]; field_simp; simp [h2p p q hp hq, h1p r hr]

  -- We show that $f(pqrs) = -f(1)$ for if $p$, $q$, $r$, $s$ are primes.
  have h4p : ∀ p q r s: ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → Nat.Prime s
      → f (p * q * r * s) =  -f 1 := by
    intro p q r s hp hq hr hs
    have t1 : p > 1 := by exact Nat.Prime.one_lt hp
    have t2 : q > 1 := by exact Nat.Prime.one_lt hq
    have t3 : r > 1 := by exact Nat.Prime.one_lt hr
    have t4 : s > 1 := by exact Nat.Prime.one_lt hs
    have : p * q * r * s > 1 := by
      have : p * q > 1 := by exact Right.one_lt_mul' t1 t2
      have : p * q * r > 1 := by exact Right.one_lt_mul' this t3
      exact Right.one_lt_mul' this t4
    obtain ⟨ t, ⟨ htp, htdvd, htf ⟩ ⟩ := h (p * q * r * s) this
    rw [htf]
    have : ((t = p ∨ t = q) ∨ t = r) ∨ t = s := by
      repeat rw [Nat.Prime.dvd_mul htp] at htdvd
      repeat rw [Nat.prime_dvd_prime_iff_eq htp] at htdvd
      . exact htdvd
      . exact hs
      . exact hr
      . exact hq
      . exact hp

    rcases this with g | g
    . rcases g with g' | g'
      . rcases g' with g'' | g''
        . rw [g'']
          have : p * q * r * s / p = q * r * s := by
            calc
              _ = q * r * s * p / p := by ring_nf
              _ = _  := by field_simp
          rw [this]; clear this
          simp [h3p q r s hq hr hs, h1p r hr, h1p p hp]; ring
        . rw [g'']
          have : p * q * r * s / q = p * r * s := by
            calc
              _ = p * r * s * q / q := by ring_nf
              _ = _  := by field_simp
          rw [this]; clear this
          simp [h3p p r s hp hr hs, h1p r hr, h1p q hq]; ring
      . rw [g']
        have : p * q * r * s / r = p * q * s := by
          calc
            _ = p * q * s * r / r := by ring_nf
            _ = _  := by field_simp
        rw [this]; clear this
        simp [h3p p q s hp hq hs, h1p r hr, h1p q hq]; ring
    . rw [g]; field_simp; simp [h3p p q r hp hq hr, h1p s hs]; ring

  -- Since 2001 is the product of three primes 3, 23, and 29,
  -- we obtain that $f(2001) = -f(1)/2$. But by assumption $f(2001)=1$.
  -- Hence, $f(1) = -2$.
  obtain h2001 := h3p 3 23 29 (by decide) (by decide) (by decide)
  simp at h2001
  rw [hf] at h2001
  field_simp at h2001

  -- Since 2002 is the product of four primes 2, 7, 11, and 13,
  -- we obtain that $f(2002) = -f(1)$. But $f(1) = -2$.
  -- Hence, $f(2002) = -(-2) = 2$, as desired.
  obtain h2002 := h4p 2 7 11 13 (by decide) (by decide) (by decide) (by decide)
  simp at h2002
  linarith
