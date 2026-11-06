import Mathlib

/- Soient $p$ et $n$ des entiers strictement positifs, avec $p$ premier, et $n \geqslant p$. On suppose que $1+n p$ est un carré parfait. Montrer que $n+1$ est une somme de $p$ carrés parfaits non nuls (non nécessairement distincts). -/
theorem number_theory_605435 {p n : ℕ} (hp : Nat.Prime p) (hn : p ≤ n)
    (h : ∃ m, m^2 = 1 + n * p) :
    ∃ s : Multiset ℕ, s.card = p ∧ (s.map (fun i => i^2)).sum = n + 1 ∧ ∀ i ∈ s, i ≠ 0 := by

-- Let $k$ be such that $1+n p=k^{2}$,
  obtain ⟨k,h⟩ := h
  have hk : 1 ≤ k := by
    by_contra hk
    simp at hk
    simp [hk] at h
    omega

-- Then $n p=(k-1)(k+1)$.
  replace h : (k - 1) * (k + 1) = n * p := by
    zify [hk] at h ⊢
    ring_nf
    rw [h]
    ring

-- So the prime number $p$ divides $k - 1$ or $k + 1$
  have h' : p ∣ (k - 1) * (k + 1) := by
    use n
    rw [h, mul_comm]
  simp [Nat.Prime.dvd_mul hp ] at h'

  rcases h' with h'|h' <;>
  obtain ⟨l,hl⟩ := h'

-- First case: $p$ divides $k-1$.
-- Then we can write $k-1=p \ell$, so $k=p \ell+1$.
  · have hk' : k = p * l + 1 := by
      zify [hk] at hl ⊢
      rw [← hl]
      group
    have hn' : n = l * (p * l + 2) := by
      rw [← mul_left_inj' hp.ne_zero]
      zify [hk] at *
      rw [← h]
      rw [hk']
      ring
-- By substituting into the equation, we get that $n+1=p \ell^{2}+2 \ell+1=(p-1) \ell^{2}+(\ell+1)^{2}$.
    use {l + 1} + (p - 1) • {l}
    constructor
    · simp
      zify [hp.one_le]
      group
    constructor
    · simp [Multiset.map_nsmul, Multiset.sum_nsmul]
      rw [hn']
      zify [hp.one_le]
      ring
    · simp
      intro _
      by_contra hl'
      simp [hl'] at hn'
      rw [hn'] at hn
      absurd hn
      simp
      exact hp.ne_zero

-- Second case: $p$ divides $k+1$.
-- Using the same method, we get $n+1=p \ell^{2}-2 \ell+1=(p-1) \ell^{2}+(\ell-1)^{2}$.
  · have hl' : 1 ≤ l := by
      by_contra hl'
      simp at hl'
      simp [hl'] at hl
    have hk' : (k:ℤ) - 1 = p * l - 2 := by
      zify at hl
      rw [← hl]
      group
    have hn' : (n:ℤ) = l * (p * l - 2) := by
      rw [← mul_left_inj' (?_ : (p:ℤ) ≠ 0)]
      zify [hk] at h hk hl
      rw [← h, hk', hl]
      ring
      norm_cast
      exact hp.ne_zero
    use {l - 1} + (p - 1) • {l}
    constructor
    · simp
      zify [hp.one_le]
      group
    constructor
    · simp [Multiset.map_nsmul, Multiset.sum_nsmul]
      zify [hp.one_le, hl']
      rw [hn']
      ring
    · simp
      constructor
      · intro hh
        have : (l:ℤ) = 1 := by
          zify [hl'] at hh
          linarith
        simp [this] at hn'
        zify at hn
        linarith
      · intro _
        intro hh
        simp [hh] at hn'
        absurd hn
        simp
        rw [hn']
        exact hp.one_le
