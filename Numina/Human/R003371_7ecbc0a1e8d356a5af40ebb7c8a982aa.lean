import Mathlib

-- we prove the case when a ≤ b ≤ c, then use symmetry to show the rest
lemma lemma_1 (a b c: ℕ) (l0: 0 < a) (l1: a ≤ b) (l2: b ≤ c) (g1: a.gcd b = 1) (g2: a.gcd c = 1)
  (d1: a ∣ a + b + c) (d2: b ∣ a + b + c) (d3: c ∣ a + b + c):
    a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 1 ∧ b = 1 ∧ c = 2 ∨ a = 1 ∧ b = 2 ∧ c = 3 := by

    -- we rewrite the divisibility conditions
      replace d3: c ∣ a + b := by
        rw [show a + b = a  + b + c - c by omega]
        apply Nat.dvd_sub
        omega
        tauto
        simp
      replace d2: b ∣ a + c := by
        rw [show a + c = a + b + c - b by omega]
        apply Nat.dvd_sub
        omega
        tauto
        simp
      replace d1: a ∣ b + c := by
        rw [show b + c = a + b + c - a by omega]
        apply Nat.dvd_sub
        omega
        tauto
        simp
      apply exists_eq_mul_right_of_dvd at d3
      obtain ⟨k, h3⟩ := d3

      have lk: k ≤ 2 := by nlinarith
      interval_cases k

      -- k = 0
      .
        simp at h3
        omega

      -- k = 1
      .
        simp at h3
        simp [← h3] at d2
        replace d2: b ∣ 2 * a := by
          rw [show 2 * a = a + (a + b) - b by omega]
          apply Nat.dvd_sub
          . omega
          . tauto
          . simp
        apply exists_eq_mul_right_of_dvd at d2
        obtain ⟨l, h2⟩ := d2
        have ll: l ≤ 2 := by nlinarith
        interval_cases l

        -- l = 0
        .
          simp at h2
          omega

        -- l = 1
        .
          simp at h2
          simp [← h2] at g1
          simp [g1] at h2
          simp [g1, h2] at h3
          omega

        -- l = 2
        .
          replace h2: a = b := by omega
          simp [h2] at g1
          simp [g1] at h2
          omega

      -- k = 2
      .
        have va: a = c := by omega
        have vb: b = c := by omega
        simp [va] at g2
        omega


/-Find all possible triples (a,b,c) of positive integers with the following properties:
gcd(a,b)=gcd(a,c)=gcd(b,c)=1;
a is a divisor of a+b+c;
b is a divisor of a+b+c;
c is a divisor of a+b+c.
(Here gcd(x,y) is the greatest common divisor of x and y.)-/

theorem number_theory_173410: {(a, b, c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a.gcd b = 1 ∧ a.gcd c = 1 ∧ b.gcd c = 1 ∧
  a ∣ a + b + c ∧ b ∣ a + b + c ∧ c ∣ a + b + c} =
  {(1, 1, 1), (1, 1, 2), (1, 2, 1), (2, 1, 1), (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)} := by

  ext ⟨a, b, c⟩
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨ha, hb, hc, g1, g2, g3, d1, d2, d3⟩
    simp

    have u: a ≤ b ∧ b ≤ c ∨ a ≤ c ∧ c ≤ b ∨ b ≤ a ∧ a ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b ∨ c ≤ b ∧ b ≤ a := by
      omega

    -- we check all possible orders of a, b, c
    rcases u with u | u | u | u | u | u

    -- case 1: a ≤ b ∧ b ≤ c
    .
      have i:= lemma_1 a b c (by omega) (by omega) (by omega) g1 g2 d1 d2 d3
      rcases i with i | i | i
      all_goals simp [i]

    -- case 2: a ≤ c ∧ c ≤ b
    .
      rw [Nat.gcd_comm] at g3
      rw [show a + b + c = a + c + b by omega] at d1 d2 d3
      have i:= lemma_1 a c b (by omega) (by omega) (by omega) g2 g1 d1 d3 d2
      rcases i with i | i | i
      all_goals simp [i]

    -- case 3: b ≤ a ∧ a ≤ c
    .
      rw [Nat.gcd_comm] at g1
      rw [show a + b + c = b + a + c by omega] at d1 d2 d3
      have i:= lemma_1 b a c (by omega) (by omega) (by omega) g1 g3 d2 d1 d3
      rcases i with i | i | i
      all_goals simp [i]

    -- case 4: b ≤ c ∧ c ≤ a
    .
      rw [Nat.gcd_comm] at g2 g1
      rw [show a + b + c = b + c + a by omega] at d1 d2 d3
      have i:= lemma_1 b c a (by omega) (by omega) (by omega) g3 g1 d2 d3 d1
      rcases i with i | i | i
      all_goals simp [i]

    -- case 5: c ≤ a ∧ a ≤ b
    .
      rw [Nat.gcd_comm] at g2 g3
      rw [show a + b + c = c + a + b by omega] at d1 d2 d3
      have i:= lemma_1 c a b (by omega) (by omega) (by omega) g2 g3 d3 d1 d2
      rcases i with i | i | i
      all_goals simp [i]

    -- case 6: c ≤ b ∧ b ≤ a
    .
      rw [Nat.gcd_comm] at g1 g3 g2
      rw [show a + b + c = c + b + a by omega] at d1 d2 d3
      have i:= lemma_1 c b a (by omega) (by omega) (by omega) g3 g2 d3 d2 d1
      rcases i with i | i | i
      all_goals simp [i]


  -- the backward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rcases h with i | i | i | i | i | i | i | i | i | i
    all_goals simp at i; simp [i]
    all_goals norm_num