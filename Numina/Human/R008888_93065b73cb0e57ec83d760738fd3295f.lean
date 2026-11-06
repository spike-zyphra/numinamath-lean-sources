import Mathlib

/- Bepaal alle paren priemgetallen $(p, q)$ zodat
$p^{2}+5 p q+4 q^{2}$ het kwadraat van een geheel getal is. -/
theorem number_theory_605991 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (IsSquare (p^2 + 5 * p * q + 4 * q^2)) ↔
    ((p = 5 ∧ q = 11) ∨ (p = 13 ∧ q = 3) ∨ (p = 7 ∧ q = 5)) := by
  constructor
  · -- write p^2 + 5pq+4q^2 = a^2.
    rintro ⟨a, ha⟩
    -- then pq = (a-p-2q)(a+p+2q)
    replace ha: (p*q:ℤ) = (a-p-2*q)*(a+p+2*q) := by
      zify at ha
      linarith only [ha]
    -- obviously, two factors > 0.
    have pos_right: 0 < a+p+2*q := by
      linarith only [hp.pos]
    zify at pos_right
    have pos_left: (0:ℤ) < a-p-2*q := by
      have: (0:ℤ) < p*q := by
        apply mul_pos
        all_goals simp [hp.pos, hq.pos]
      rw [ha] at this
      exact (pos_iff_pos_of_mul_pos this).mpr pos_right
    -- since p,q are prime, and a+p+2q > p,q,
    -- only case is a+p+2q = pq.
    have h1: a+p+2*q = (p*q:ℤ) := by
      have hp': Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
      have h1: (p:ℤ) ∣ p*q := by
        apply Int.dvd_mul_right
      rw [ha] at h1
      rcases (Prime.dvd_or_dvd hp' h1) with h2 | h2
      · -- if p divide a-p-2q, then p ≤ a-p-2q
        have ple: (p:ℤ) ≤ a-p-2*q := by
          apply Int.le_of_dvd pos_left h2
        -- therefore a+p+2q ≤ q
        have leq: (a:ℤ) + p + 2*q ≤ q := by
          have: (p:ℤ)*(a+p+2*q) ≤ p*q := by
            rw [ha]
            exact (Int.mul_le_mul_iff_of_pos_right pos_right).mpr ple
          apply Int.le_of_mul_le_mul_left this (by simp [hp.pos])
        -- but a+p+2q > q, contradiction
        norm_cast at leq
        linarith only [leq, hp.pos]
      · -- p ∣ a+p+2q, then a+p+2q = kp
        rcases h2 with ⟨k, hk⟩
        rw [hk] at ha
        have kpos: 0 < k := by
          rw [hk] at pos_right
          have: 0 < (p:ℤ) := by simp [hp.pos]
          exact (pos_iff_pos_of_mul_pos pos_right).mp this
        -- kp (a-p-2q) = pq, so k(a-p-2q) = q, or k divide q.
        have kdvd: k ∣ q := by
          use (a-p-2*q)
          have hh1: p*q = p*(k*(a-p-2*q)) := by
            rw [ha]; ring
          have hh2: (p:ℤ) ≠ 0 := by simp [hp.ne_zero]
          simp only [mul_eq_mul_left_iff, hh2, or_false] at hh1
          exact hh1
        -- then k = 1 or q.
        obtain (keq | keq): k = 1 ∨ k = q := by
          rw [Int.ofNat_dvd_right] at kdvd
          rw [← Int.natAbs_of_nonneg (le_of_lt kpos)]
          norm_cast
          apply (Nat.dvd_prime hq).mp kdvd
        · -- impossible for k = 1, otherwise a+p+2q = p
          rw [keq, mul_one] at hk
          linarith only [hk, hq.pos]
        · -- k = q, exactly a+p+2q = pq
          rw [hk, keq]
    -- and then a-p-2q = 1
    have h2: a-p-2*q = (1:ℤ) := by
      rw [h1] at ha
      apply Int.eq_one_of_mul_eq_self_left ?_ ha.symm
      symm; apply ne_of_lt
      simp [hp.pos, hq.pos]
    -- sub two equations:
    -- pq-1 = (a+p+2q) - (a-p-2q) = 2p+4q
    -- so pq-2p-4q-1 = 0, pq-2p-4q+8 = 9.
    -- or, (p-4)(q-2) = 9
    have h3: (p-4:ℤ)*(q-2) = 9 := by
      linarith only [h1, h2]
    -- both p-4, q-2 > 0.
    replace pos_right: q-2 > (0:ℤ) := by
      apply lt_of_le_of_ne
      · simp [hq.two_le]
      · by_contra!
        simp [← this] at h3
    replace pos_left: (p:ℤ) - 4 > 0 := by
      have: 0 < (9:ℤ) := by norm_num
      rw [← h3] at this
      exact (pos_iff_pos_of_mul_pos this).mpr pos_right
    -- then p-4 = 1,9,3; q-2 = 9,1,3.
    have {m n: ℤ} (hm: 0 < m) (hn: 0 < n) (heq: m*n = 9):
      (m=1 ∧ n = 9) ∨ (m=9 ∧ n=1) ∨ (m=3 ∧ n = 3) := by
      have mdvd: m.natAbs ∣ 3^2 := by
        zify
        simp only [Int.reducePow, abs_dvd, ← heq]
        apply Int.dvd_mul_right
      rw [Nat.dvd_prime_pow (by norm_num)] at mdvd
      rw [← Int.natAbs_of_nonneg (le_of_lt hm),
      ← Int.natAbs_of_nonneg (le_of_lt hn)] at heq ⊢
      rcases mdvd with ⟨k, kle, hk⟩
      rw [hk] at heq ⊢
      interval_cases k
      all_goals
        norm_num at heq ⊢
        linarith only [heq]
    replace := this pos_left pos_right h3
    -- (p-4,q-2) = (1,9), (9,1), (3,3)
    -- then (p,q) = (5,11), (13,3), (7,5)
    revert this; apply Or.imp3
    all_goals exact fun ⟨h4,h5⟩ =>
      ⟨(by linarith only [h4]), (by linarith only [h5])⟩
  · -- verification
    rintro (⟨rfl,rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- 784 = 28^2
      use 28; norm_num
    · -- 400 = 20^2
      use 20; norm_num
    · -- 324 = 18^2
      use 18; norm_num