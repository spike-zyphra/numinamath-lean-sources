import Mathlib


open scoped Nat

/- for positive x,n, x ≤ (x !)^n  -/
lemma l_le_self_factorial_pow {x n: ℕ} (hn: 0 < n):
  x ≤ (x !)^n := by
  have h1: (x !) ≤ (x !)^n := by
    apply Nat.le_self_pow hn.ne'
  have h2: x ≤ x ! := by
    exact Nat.self_le_factorial x
  exact h2.trans h1

/- Let $A$ be a positive integer. Let $a, b, c, d$ be positive integers. Suppose that $(a!)^A + (b!)^A = (c!)^A + (d!)^A$. Show that $a \cdot b = c \cdot d$. -/
theorem number_theory_638980 {A : ℕ} (hA : A > 0) {a b c d : ℕ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)
    (h : (a !)^A + (b !)^A = (c !)^A + (d !)^A) : a * b = c * d := by

  -- we may suppose a ≥ b, c ≥ d
  wlog hab: a ≥ b
  · specialize this hA hb ha hc hd
    rw [mul_comm a b]
    nth_rw 1 [add_comm] at this
    apply this h
    push_neg at hab
    exact hab.le

  wlog hcd: c ≥ d
  · specialize this hA ha hb hd hc
    rw [mul_comm c d]
    nth_rw 2 [add_comm] at this
    apply this h hab
    push_neg at hcd
    exact hcd.le

  -- a ≥ b, so a ! ≥ b !, (a !)^A ≥ (b !)^A
  have h1: (a !)^A + (b !)^A ≤ 2 * (a !)^A := by
    suffices (b !)^A ≤ (a !)^A by
      linarith only [this]
    apply Nat.pow_le_pow_left
    exact Nat.factorial_le hab

  -- similarly, (c !)^A + (d !)^A ≤ 2 (c !)^A
  have h2: (c !)^A + (d !)^A ≤ 2 * (c !)^A := by
    suffices (d !)^A ≤ (c !)^A by
      linarith only [this]
    apply Nat.pow_le_pow_left
    exact Nat.factorial_le hcd

  -- if a < c, then c ! ≥ (a+1) a !
  have h3 {x y: ℕ} (hxy: x < y) (hx: 0 < x) (hy: 0 < y):
    (x+1)^A * (x !)^A ≤ (y !)^A := by
    rw [← Nat.mul_pow, ← Nat.factorial_succ]
    apply Nat.pow_le_pow_left
    exact Nat.factorial_le hxy

  -- if (x !)^A + (y !)^A = 2, x > 0, y > 0, then x = 1, y = 1.
  have case_eq_one {x y: ℕ} (hx: 0 < x) (hy: 0 < y)
    (heq: (x !)^A + (y !)^A = 2): x = 1 ∧ y = 1 := by
    have hx': 0 < (x !)^A := by
      apply Nat.pow_pos (Nat.factorial_pos x)
    have hy': 0 < (y !)^A := by
      apply Nat.pow_pos (Nat.factorial_pos y)
    have hh1: (x !)^A < (x !)^A + (y !)^A := by
      simp [hy']
    have hh2: (y !)^A < (x !)^A + (y !)^A := by
      simp [hx']
    rw [heq] at hh1 hh2
    have xeq': (x !)^A = 1 := by omega
    have yeq': (y !)^A = 1 := by omega
    have xle: x ≤ 1 := by
      rw [← xeq']
      apply l_le_self_factorial_pow hA
    have yle: y ≤ 1 := by
      rw [← yeq']
      apply l_le_self_factorial_pow hA
    omega

  -- a=1 or c = 1, trivial.
  by_cases ha1: a = 1
  · have beq: b = 1 := by omega
    have cdeq: c = 1 ∧ d = 1 := by
      apply case_eq_one hc hd
      simp [← h, ha1, beq]
    simp [ha1, beq, cdeq]
  by_cases hc1: c = 1
  · have deq: d = 1 := by omega
    have abeq: a = 1 ∧ b = 1 := by
      apply case_eq_one ha hb
      simp [h, hc1, deq]
    simp [hc1, deq, abeq]

  -- we claim cannot be the case a < c or c < a
  have hac1: ¬ a < c := by
    have age: a ≥ 2 := by omega
    have age': (a+1)^A > 2 := by
      have: (a+1)^A ≥ a+1 := by
        apply Nat.le_self_pow hA.ne'
      apply lt_of_lt_of_le ?_ this
      omega
    rintro hac
    specialize h3 hac ha hc
    replace h3: (c !)^A > 2 * (a !)^A := by
      apply lt_of_lt_of_le ?_ h3
      refine Nat.mul_lt_mul_of_pos_right age' ?_
      apply Nat.pow_pos (Nat.factorial_pos a)
    have := lt_of_le_of_lt h1 h3
    rw [h] at this
    simp at this
  have hac2: ¬ c < a := by
    have cge: c ≥ 2 := by omega
    have cge': (c+1)^A > 2 := by
      have: (c+1)^A ≥ c+1 := by
        apply Nat.le_self_pow hA.ne'
      apply lt_of_lt_of_le ?_ this
      omega
    rintro hac
    specialize h3 hac hc ha
    replace h3: (a !)^A > 2 * (c !)^A := by
      apply lt_of_lt_of_le ?_ h3
      refine Nat.mul_lt_mul_of_pos_right cge' ?_
      apply Nat.pow_pos (Nat.factorial_pos c)
    have := lt_of_le_of_lt h2 h3
    rw [← h] at this
    simp at this

  -- therefore a = c
  have aeqc: a = c := by
    push_neg at hac1 hac2
    apply le_antisymm hac2 hac1
  -- and it follows that b = d
  simp only [aeqc, Nat.add_left_cancel_iff, zero_le] at h
  replace h: b = d := by
    have: b ! = d ! := by
      rwa [pow_left_inj₀] at h
      <;> simp [hA.ne']
    by_cases hhb: b = 1
    · simp only [hhb, Nat.factorial_one] at this
      have dle: d < 2 := by
        by_contra! dge
        have hh1: d ≤ d ! := Nat.self_le_factorial d
        rw [← this] at hh1
        linarith only [dge, hh1]
      rw [hhb]
      omega
    · rwa [← Nat.factorial_inj (by omega)]
  -- so ab = cd
  simp [aeqc, h]