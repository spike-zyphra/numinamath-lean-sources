import Mathlib

/- 5. (Austria-Poland Olympiad 2000) Find all positive integers $N$, such that $N$ has only the prime factors 2 and 5, and $N+25$ is a perfect square. -/

-- if primefcotrs are subset of {2, 5} can write as product
lemma l_primefactor_mul_of_subset (n : ℕ) (h : n ≠ 0) (h' : n.primeFactors ⊆ {2, 5}) :
    n = 2^(n.factorization 2) * 5^(n.factorization 5) := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self h]
  rw [Finsupp.prod_of_support_subset (s := {2, 5})]
  . simp
  . simpa
  . simp

-- if primefcotrs are {2, 5} can write as product with positive pwoers
lemma l_primefactor_mul_of_eq (n : ℕ) (h : n ≠ 0) (h' : n.primeFactors = {2, 5}) :
    n = 2^(n.factorization 2) * 5^(n.factorization 5) ∧ 0 < n.factorization 2 ∧ 0 < n.factorization 5 := by
  and_intros
  . nth_rw 1 [← Nat.factorization_prod_pow_eq_self h]
    simp [Finsupp.prod, h']
  all_goals (
    refine Nat.Prime.factorization_pos_of_dvd ?_ h ?_
    . norm_num
    . apply Nat.dvd_of_mem_primeFactors
      rw [h']
      simp
  )

-- if N + 25 is square then N = x * (x + 10)
lemma l_square_add_twenty_five (N : ℕ) (h : IsSquare (N + 25)) : ∃ x, N = x * (x + 10) := by
  obtain ⟨y, hy⟩ := h
  have hy' : 5 ≤ y := by
    apply Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num) |>.mp
    linarith
  use y - 5
  rw [show y - 5 + 10 = y + 5 by omega]
  rw [mul_comm, ← Nat.sq_sub_sq]
  ring_nf at hy ⊢
  omega

-- if p ^2 doesn't divde 10 then one of x, x+10's padicvalue at p is <= 1
lemma l_div_ten (x p: ℕ) (hp : ¬ p^2 ∣ 10) : x.factorization p ≤ 1 ∨ (x + 10).factorization p ≤ 1 := by
  by_contra h
  push_neg at h
  have h1 := Nat.ordProj_dvd x p
  have h2 := Nat.ordProj_dvd (x + 10) p
  have h3 : p^2 ∣ p ^ x.factorization p := by
    apply pow_dvd_pow
    linarith
  have h4 : p^2 ∣ p ^ (x + 10).factorization p := by
    apply pow_dvd_pow
    linarith
  simp at h3 h4
  have h5 : p^2 ∣ x := by apply Nat.dvd_trans h3 h1
  have h6 :p ^ 2 ∣ x + 10 := by apply Nat.dvd_trans h4 h2
  have : p^2 ∣ 10 := by exact (Nat.dvd_add_iff_right h5).mpr h6
  contradiction

-- if p divides 10, then padicval at x being 0 and at x + 10 being 0 are equivalent
lemma l_div_ten' (x p: ℕ) (hx : x ≠ 0) (hp : p ∣ 10) (hp' : Nat.Prime p) : x.factorization p = 0 ↔ (x + 10).factorization p = 0 := by
  constructor <;> rintro h
  . apply Nat.factorization_eq_zero_of_not_dvd
    by_contra h'
    have : p ∣ x := by exact (Nat.dvd_add_iff_left hp).mpr h'
    rw [Nat.Prime.dvd_iff_one_le_factorization hp' hx] at this
    linarith
  . apply Nat.factorization_eq_zero_of_not_dvd
    by_contra h'
    have : p ∣ (x + 10) := by exact (Nat.dvd_add_iff_right h').mp hp
    rw [Nat.Prime.dvd_iff_one_le_factorization hp' (by linarith)] at this
    linarith

-- following diaphantine equation has 0 only at b = 1 as a = 0, 1 are not possible, a = 2 gives b = 1, for bigger a, taking modulo 4 we get contradiction
lemma l_eq_1 (a b : ℕ) (h : 2 ^ a * 5 = 10 + 2 * 5 ^ b) : b = 1 := by
  match a with
  | 0 =>
    simp at h
    omega
  | 1 => simp at h
  | 2 =>
    simp at h
    have : 5 ^ b = 5 ^ 1 := by linarith
    apply le_antisymm
    . rw [← Nat.pow_le_pow_iff_right (show 1 < 5 by norm_num)]
      linarith
    . rw [← Nat.pow_le_pow_iff_right (show 1 < 5 by norm_num)]
      linarith
  | k + 3 =>
    have : b ≠ 0 := by
      by_contra h'
      rw [h'] at h
      simp at h
      omega
    rw [show b = (b - 1) + 1 by omega] at h
    ring_nf at h
    replace h : 2 ^ k * 4 = 1 + 5 ^ (b - 1) := by linarith
    replace h : (2 : ZMod 4) ^ k * 4 = 1 + 5 ^ (b - 1) := by
      norm_cast
      rw [h]
    ring_nf at h
    rw [show (4 : ZMod 4) = 0 by norm_cast, show (5 : ZMod 4) = 1 by norm_cast] at h
    simp at h
    norm_cast at h

-- following diaphantine equation has 0 only at a = 0, taking modulo 5, 8 we get a = 0 and otherwise contradiction
lemma l_eq_2 (a b : ℕ) (h : 2 * 5 ^ (a + 2) = 2 ^ b * 5 + 10) : a = 0 := by
  have : b ≠ 0 := by
    by_contra h'
    rw [h'] at h
    omega
  rw [show b = (b - 1) + 1 by omega] at h
  ring_nf at h
  replace h : 5 ^ a * 5 = 1 + 2 ^ (b - 1) := by linarith
  have : Even (b - 1) := by
    rw [← Nat.not_odd_iff_even]
    by_contra h'
    obtain ⟨k, hk⟩ := h'
    rw [hk] at h
    have : (5 : ZMod 5) ^ a * 5 = 1 + 2 ^ (2 * k + 1) := by
      norm_cast
      rw [h]
    ring_nf at this
    rw [show (5 : ZMod 5) = 0 by norm_cast] at this
    simp at this
    rw [mul_comm k, pow_mul, show (2 ^ 2 : ZMod 5) = -1 by norm_cast] at this
    obtain h' | h' := neg_one_pow_eq_or (R := ZMod 5) k <;> (rw [h'] at this; norm_cast at this)
  obtain ⟨c, hc⟩ := this
  rw [hc] at h
  match c with
  | 0 => simp at h; omega
  | 1 =>
    simp at h
    by_contra h'
    have := Nat.one_lt_pow h' (show 1 < 5 by norm_num)
    linarith
  | k + 2 =>
    ring_nf at h
    rw [mul_comm k, pow_mul] at h
    ring_nf at h
    have : Odd a := by
      rw [← Nat.not_even_iff_odd]
      by_contra h'
      obtain ⟨l, hl⟩ := h'
      rw [hl] at h
      ring_nf at h
      rw [mul_comm l, pow_mul] at h
      ring_nf at h
      have : (25 : ZMod 8) ^ l * 5 = 1 + 4 ^ k * 16 := by norm_cast; rw [h]
      rw [show (25 : ZMod 8) = 1 by norm_cast, show (16 : ZMod 8) = 0 by norm_cast] at this
      simp at this
      norm_cast
    obtain ⟨l, hl⟩ := this
    rw [hl] at h
    replace h : (5 ^ (l + 1) + 2 ^ (k + 2)) * (5 ^ (l + 1) - 2 ^ (k + 2)) = 1 := by
      rw [← Nat.sq_sub_sq]
      ring_nf at h ⊢
      rw [mul_comm k, pow_mul 2]
      ring_nf
      omega
    simp at h
    have h1 : 1 < 5 ^ (l + 1) := Nat.one_lt_pow (by linarith) (show 1 < 5 by norm_num)
    have h2 : 1 < 2 ^ (k + 2) := Nat.one_lt_pow (by linarith) (show 1 < 2 by norm_num)
    have h := h.left
    linarith

theorem number_theory_239914 {N : ℕ} (hN : N > 0) :
    N.primeFactors = {2, 5} ∧ IsSquare (N + 25) ↔ N = 200 ∨ N = 2000 := by
  constructor
  . rintro ⟨hp, hs⟩
    -- write N = x * (x+10) and write all 3 as 2 ^ a * 5 ^ b
    obtain ⟨hab, ha_pos, hb_pos⟩ := l_primefactor_mul_of_eq N (by linarith) hp
    obtain ⟨x, hx⟩ := l_square_add_twenty_five N hs
    have hx' : 0 < x := by simpa [hx] using hN
    have hx_primeFactors : x.primeFactors ⊆ {2, 5} := by
      rw [← hp]
      apply Nat.primeFactors_mono (by simp [hx]) (by linarith)
    have hab1 := l_primefactor_mul_of_subset x (by linarith) hx_primeFactors
    have hx_primeFactors' : (x + 10).primeFactors ⊆ {2, 5} := by
      rw [← hp]
      apply Nat.primeFactors_mono (by simp [hx]) (by linarith)
    have hab2 := l_primefactor_mul_of_subset (x + 10) (by linarith) hx_primeFactors'
    have ha_add : Nat.factorization x 2 + Nat.factorization (x + 10) 2 = Nat.factorization N 2 := by
      rw [hx, Nat.factorization_mul (by linarith) (by linarith)]
      simp
    have hb_add : Nat.factorization x 5 + Nat.factorization (x + 10) 5 = Nat.factorization N 5 := by
      rw [hx, Nat.factorization_mul (by linarith) (by linarith)]
      simp
    -- padival at 2, 5 of x, x+10 are nonzero and at least one is <= 1
    have h2 := l_div_ten x 2 (by norm_num)
    have h5 := l_div_ten x 5 (by norm_num)
    have h2' : Nat.factorization x 2 ≠ 0 ∧ Nat.factorization (x + 10) 2 ≠ 0 := by
      simp
      rw [l_div_ten' _ _ (by linarith) (by norm_num) (by norm_num)]
      simp
      by_contra h
      rw [h, l_div_ten' _ _ (by linarith) (by norm_num) (by norm_num) |>.mpr h] at ha_add
      linarith
    have h5' : Nat.factorization x 5 ≠ 0 ∧ Nat.factorization (x + 10) 5 ≠ 0 := by
      simp
      rw [l_div_ten' _ _ (by linarith) (by norm_num) (by norm_num)]
      simp
      by_contra h
      rw [h, l_div_ten' _ _ (by linarith) (by norm_num) (by norm_num) |>.mpr h] at hb_add
      linarith
    obtain h2 | h2 := h2
    -- if padic val of x at 2 is <= 1, then it's 0 or 1
    . interval_cases h2_v : x.factorization 2
      -- 0 is not possible
      . simp at h2'
      -- if 1 then we get l_eq_1
      . have : x.factorization 5 = 1 := by
          by_contra h
          have : (x + 10).factorization 5 = 1 := by omega
          rw [this] at hab2
          simp at hab1 hab2
          have := l_eq_1 ((x + 10).factorization 2) (x.factorization 5)
          rw [← hab1, ← hab2, add_comm] at this
          simp at this
          contradiction
        rw [this] at hab1
        left
        rw [hab1] at hx
        norm_num at hx; assumption
    -- if x +10's padival at 2 <=1 it is 0 or 1
    . interval_cases h2_v : (x + 10).factorization 2
      -- 0 not possible
      . simp at h2'
      -- if 1 then x + 10's padicval at 5 can't be 0 or 1
      . match h' : (x + 10).factorization 5 with
        | 0 => simp [h'] at h5'
        | 1 =>
          rw [h'] at hab2
          linarith
          -- if k + 2, we get l_eqn_2
        | k + 2 =>
          rw [h'] at h5
          simp at h5
          have : x.factorization 5 = 1 := by omega
          rw [this] at hab1
          have : 2 * 5 ^ (k + 2) = 2 ^ (x.factorization 2) * 5 + 10 := by
            rw [h', hab1, eq_comm] at hab2
            convert hab2
          have : k = 0 := l_eq_2 _ _ this
          rw [this] at h'
          rw [h'] at hab2
          ring_nf at hab2
          have : x = 40 := by linarith
          rw [this] at hx
          right
          norm_num at hx
          simp [hx]
  -- for 20, 20000 just plug in
  . rintro h
    obtain rfl | rfl := h
    . and_intros
      . rw [show 200 = 2 ^ 3 * 5 ^ 2 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
            Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
            Nat.primeFactors_prime_pow (by norm_num) (by norm_num)]
        ext i; simp
      . use 15
    . and_intros
      . rw [show 2000 = 2 ^ 4 * 5 ^ 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
            Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
            Nat.primeFactors_prime_pow (by norm_num) (by norm_num)]
        ext i; simp
      . use 45