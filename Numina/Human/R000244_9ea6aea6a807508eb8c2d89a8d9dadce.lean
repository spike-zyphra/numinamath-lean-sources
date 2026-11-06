import Mathlib


/-
  For which positive integers  $m$  does there exist an infinite arithmetic sequence of integers  $a_1, a_2, . . .$  and an infinite geometric sequence of integers  $g_1, g_2, . . .$  satisfying the following properties?
  - $a_n - g_n$  is divisible by  $m$  for all integers  $n \ge 1$ ;
  - $a_2 - a_1$  is not divisible by  $m$ .

  *Holden Mui*
-/

theorem number_theory_8683 (m : ℕ+): (∃ a g : ℕ+ → ℤ, (∃ d, ∀ n, a (n + 1) = (a n) + d) ∧ (∃ q : ℝ, q > 0 ∧ ∀ n, g (n + 1) = (g n) * q)
    ∧ (∀ n, ↑m ∣ (a n) - (g n)) ∧ ¬ ↑m ∣ (a 2) - (a 1)) ↔ ¬ Squarefree m.val := by

  -- prove that if m is not squarefree, then ∃ prime p, p^2 ∣ m
  have squarefree (m : ℕ) (hm : ¬ Squarefree m) : ∃ p, Nat.Prime p ∧ p * p ∣ m := by
    apply (Iff.not Nat.squarefree_iff_prime_squarefree).mp at hm
    push_neg at hm
    exact hm

  -- prove that (1+a)^n ≡ 1+ na [mod a^2]
  have binomial_mod (n : ℕ) (a : ℕ) : (1 + a) ^ n ≡ 1 + n * a [MOD (a * a)] := by
    induction n with
    | zero => simp; exact rfl
    | succ k ih =>
      have : (1 + a) ^ k * (1 + a) ≡ (1 + k * a) * (1 + a) [MOD (a * a)] := by exact Nat.ModEq.mul ih rfl
      rw [Nat.pow_add_one]
      apply Nat.ModEq.trans this
      have : k * (a * a) ≡ 0 [MOD (a * a)]:= by refine Nat.modEq_zero_iff_dvd.mpr ?_; exact Nat.dvd_mul_left (a * a) k
      calc
        (1 + k * a) * (1 + a) = 1 + (k + 1) * a + k * (a * a) := by linarith
        _ ≡ 1 + (k + 1) * a + 0 [MOD (a * a)] := by exact Nat.ModEq.add_left (1 + (k + 1) * a) this

  -- prove that if a is squarefree and a ∣ b^2, then a ∣ b
  have squarefree_to_dvd (a b : ℕ) (h : Squarefree a) (ha : a ≠ 0) (hb : a ∣ b * b) : a ∣ b := by
      apply Nat.squarefree_iff_factorization_le_one ha |>.mp at h
      apply (Nat.dvd_iff_prime_pow_dvd_dvd b a).mpr
      intro p k hp hdvd
      match k with
      | 0 => simp
      | 1 =>
        simp at hdvd ⊢
        have : p ∣ b * b := by exact Nat.dvd_trans hdvd hb
        apply (Nat.Prime.dvd_mul hp).mp at this
        rcases this <;> trivial
      | k + 2 =>
        have : k + 2 ≤ 1 := by
          apply Nat.le_trans ?_ (h p)
          apply (Nat.Prime.pow_dvd_iff_le_factorization hp ha).mp hdvd
        linarith

  constructor
  · intro hm
    -- first, prove that m ∣ d * d
    obtain ⟨a, ⟨g, ⟨⟨d, harith⟩, ⟨⟨q, ⟨_, hgeo⟩⟩, ⟨hmid, hnmid⟩⟩⟩⟩⟩ := hm
    have h3 : g 3 ≡ a 3 [ZMOD m] := by exact Int.modEq_iff_dvd.mpr (hmid 3)
    have h2 : g 2 ≡ a 2 [ZMOD m] := by exact Int.modEq_iff_dvd.mpr (hmid 2)
    have h1 : g 1 ≡ a 1 [ZMOD m] := by exact Int.modEq_iff_dvd.mpr (hmid 1)
    have hmul1 : (g 3) * (g 1) ≡ (a 3) * (a 1) [ZMOD m] := by exact Int.ModEq.mul h3 h1
    have hmul2 : (g 2) * (g 2) ≡ (a 2) * (a 2) [ZMOD m] := by exact Int.ModEq.mul h2 h2
    have hg3 : g 3 = (g 2) * q := by
      rw [<-hgeo 2]
      congr
    have hg2 : g 2 = (g 1) * q := by
      rw [<-hgeo 1]
      congr
    have hgeo : (g 2) * (g 2) - (g 3) * (g 1) = 0 := by
      simp [<-@Int.cast_inj ℝ]
      rw [hg3, hg2]
      ring
    let a₂ := a 2
    have ha1 : a 1 = a₂ - d := by
      simp [a₂]
      rw [show (2 : ℕ+) = 1 + 1 by decide, harith 1]
      simp
    have ha3 : a 3 = a₂ + d := by
      simp [a₂]
      rw [<-harith 2]
      congr
    have harith : (a 2) * (a 2) - (a 3) * (a 1) = d * d := by rw [ha1, ha3]; ring
    have hmul2 : d * d ≡ 0 [ZMOD m] := by rw [<-hgeo, <-harith]; exact Int.ModEq.sub (Int.ModEq.symm hmul2) (Int.ModEq.symm hmul1)
    have hdvd' : ↑m ∣ d.natAbs * d.natAbs := by
      rw [<-Int.natAbs_mul]
      exact Int.ofNat_dvd_left.mp <| Int.dvd_of_emod_eq_zero hmul2
    -- by contradiction and lemma squarefree_to_dvd, we show that m ∣ d
    by_contra hsf
    obtain hdvd := squarefree_to_dvd m d.natAbs hsf (PNat.ne_zero m) hdvd'
    apply Int.ofNat_dvd_left.mpr at hdvd
    simp [ha1] at hnmid
    contradiction
  · intro hm
    -- claim that ∃ p, m = k * p^2
    obtain ⟨p, ⟨hp, ⟨k, hmul⟩⟩⟩ := squarefree m hm
    -- construct the corresponding sequences using p
    let a (n : ℕ+) : ℤ := 1 + n * k * p
    let g (n : ℕ+) : ℤ := (1 + k * p) ^ n.val
    use a, g
    split_ands
    · -- a is a arithmetic sequence
      use k * p
      intro n
      simp [a, add_mul]
      linarith
    · -- g is a geometric sequence
      use 1 + k * p
      constructor
      · rw [<-Nat.cast_mul]
        norm_cast
        exact Fin.size_pos'
      · intro n
        simp [g]
        norm_cast
    · -- verify $a_n - g_n$  is divisible by  $m$  for all integers  $n \ge 1$
      intro n
      simp [a, g]
      have h := binomial_mod n (k * p)
      apply Nat.modEq_iff_dvd.mp at h
      simp at h
      rw [mul_assoc]
      apply Int.dvd_trans ?_ h
      use k
      simp [hmul]
      ring
    · -- verify m ∤ a_2 - a_2
      by_contra hdvd
      obtain ⟨c, hc⟩ := hdvd
      simp [a] at hc
      rw [hmul, <-Int.one_mul (k * p), mul_assoc, <-Int.sub_mul, show (2 : ℤ) - 1 = 1 by decide, one_mul, mul_comm] at hc
      simp [Int.cast_mul, mul_assoc] at hc
      rcases hc with hl | hr
      · rw [mul_comm] at hl
        nth_rw 1 [<-mul_one k] at hl
        rw [Nat.cast_mul k 1] at hl
        simp only [Nat.cast_mul, mul_assoc] at hl
        have : (k : ℤ) ≠ 0 := by
          by_contra heq
          norm_cast at heq
          rw [heq] at hmul
          simp at hmul
        have : (1 : ℤ) = c * ↑p := by apply (Int.mul_eq_mul_left_iff this).mp at hl; norm_cast at hl
        have : (p : ℤ) = 1 := by refine Int.eq_one_of_mul_eq_one_left ?H <| Eq.symm this; exact Int.ofNat_zero_le p
        norm_cast at this
        have : p ≠ 1 := by exact Nat.Prime.ne_one hp
        contradiction
      · have : p > 0 := by exact Nat.Prime.pos hp
        linarith
