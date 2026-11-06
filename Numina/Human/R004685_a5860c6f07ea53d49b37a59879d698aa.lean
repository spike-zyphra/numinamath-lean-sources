import Mathlib

/-Let f(n) be a strictly increasing function defined on the set of natural numbers and taking natural number values, with f(2)=2, and when
m and n are coprime, f(mn)=f(m)f(n). Prove that for all natural numbers
f(n)=n.-/

theorem number_theory_300674 (f : ℕ → ℕ) (l: ∀ m n, m < n → f m < f n) (h2 : f 2 = 2)
  (h : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n): ∀ n, f n = n := by

  -- we show that f(3) = 3 firstly
  have h3: f 3 = 3 := by
    have i:= l 2 3 (by omega)
    suffices f 3 < 4 by omega
    have s1:= h 3 5 (by norm_num)
    simp at s1
    have s2:= l 15 18 (by omega)
    have s3:= h 2 9 (by norm_num)
    simp at s3
    simp [s3, s1] at s2
    have s4:= l 9 10 (by omega)
    have s5:= h 2 5 (by norm_num)
    simp at s5
    simp [s5, h2] at s4
    nlinarith [s2, s4]

  -- we show f 0 = 0
  have h0: f 0 = 0 := by
    have l':= l 0 1 (by omega)
    have l'':= l 1 2 (by omega)
    omega

  -- we show f 1 = 1
  have h1: f 1 = 1 := by
    have l':= l 0 1 (by omega)
    have l'':= l 1 2 (by omega)
    omega

  -- then we prove by contradiction

  -- we first obtain the least n such that f n ≠ n
  by_contra! g
  set s:= {n | f n ≠ n} with hs
  set n0 := sInf s with hn0
  have sn: n0 ∈ s ∧ ∀ y ∈ s, n0 ≤ y := by
    have i: BddBelow s := by
      use 0
      intro y ly
      simp [s] at ly
      omega
    constructor
    .
      rw [hn0]
      apply Nat.sInf_mem
      obtain ⟨p, hp⟩ := g
      use p
      simp [s]
      tauto
    .
      rw [hn0]
      intro y sy
      apply csInf_le_of_le i sy (by simp)

  simp [s] at sn
  rcases sn with ⟨g1, g2⟩
  clear hs hn0
  clear_value n0 s

  -- rewrite g2 in a more convenient form
  replace g2: ∀ m, m < n0 → f m = m := by
    intro m lm
    by_contra! u
    specialize g2 m u
    omega

  -- firstly, 4 ≤ n0
  have ln: 4 ≤ n0 := by
    by_contra! o
    interval_cases n0
    .
      omega
    .
      omega
    .
      omega
    .
      omega

  -- then for any m ≥ n0, f m > m
  have g3: ∀ m, n0 ≤ m → m < f m := by
    intro m lm
    induction' m with m ih
    .
      omega
    .
      by_cases v: n0 = m + 1
      .
        rw [← v]
        specialize g2 (n0 - 1) (by omega)
        have l':= l (n0 - 1) n0 (by omega)
        rw [g2] at l'
        omega
      .
        replace v: n0 ≤ m := by omega
        simp [v] at ih
        have l':= l m (m + 1) (by omega)
        omega

  -- then we derive contradiction by the parity of n0
  by_cases o: Odd n0

  -- case1: n0 is odd
  .
    have cp: Nat.Coprime 2 (n0 - 2) := by
      rw [Nat.Prime.coprime_iff_not_dvd]
      by_contra! v
      replace v: 2 ∣ n0 := by
        rw [show n0 = 2 + (n0 - 2) by omega]
        apply Nat.dvd_add
        .
          norm_num
        .
          tauto
      rw [← even_iff_two_dvd] at v
      absurd o
      simp [v]
      norm_num
    specialize h 2 (n0 - 2) cp
    specialize g2 (n0 - 2) (by omega)
    simp [g2, h2] at h
    specialize g3 (2 * (n0 - 2)) (by omega)
    omega

  -- case2: n0 is even
  .
    simp at o
    have cp: Nat.Coprime 2 (n0 - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd]
      by_contra! v
      replace v: 2 ∣ n0 + 1:= by
        rw [show n0 + 1 = 2 + (n0 - 1) by omega]
        apply Nat.dvd_add
        .
          norm_num
        .
          tauto
      rw [← even_iff_two_dvd] at v
      absurd v
      simp
      rw [Nat.odd_add']
      simp [o]
      norm_num
    specialize h 2 (n0 - 1) cp
    specialize g2 (n0 - 1) (by omega)
    simp [g2, h2] at h
    specialize g3 (2 * (n0 - 1)) (by omega)
    omega