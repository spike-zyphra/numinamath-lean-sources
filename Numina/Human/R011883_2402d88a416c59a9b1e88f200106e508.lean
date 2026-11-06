import Mathlib

theorem Int.mul_add_emod_self_left : ∀ (a b c : ℤ), (a * b + c) % a = c % a := sorry

/-1. Find all pairs of positive integers $(k, n)$ such that $\left(7^{k}-3^{n}\right) \mid\left(k^{4}+n^{2}\right)$-/
theorem number_theory_297774 (k n : ℕ) (kpos : 0 < k) (npos : 0 < n) :
(7 : ℤ) ^ k - 3 ^ n ∣ k ^ 4 + n ^ 2 ↔ (k = 2 ∧ n = 4) := by
-- Assume the lemma that the sum of squares of two odd numbers modulo $4$ is $2$
  have oddsq : ∀ x y : ℤ, Odd x → Odd y → (x ^ 2 + y ^ 2) % 4 = 2 := by
    intro x y xpar ypar; rcases xpar with ⟨x', hx'⟩
    rcases ypar with ⟨y', hy'⟩
    rw [hx', hy']; calc
      _ = (4 * (x' ^ 2 + x' + y' ^ 2 + y') + 2) % 4 := by ring_nf
      _ = _ := by rw [Int.mul_add_emod_self_left]; rfl
-- Prove the following three auxillary lemmas for later use
  have lm1 : ∀ a ≥ 4, 8 * a ^ 4 < 7 ^ a := by
    intro a age; induction a with
    | zero => simp at age
    | succ a ih =>
      by_cases h : a < 4
      · replace h : a = 3 := by omega
        norm_num [h]
      push_neg at h; specialize ih h; calc
        _ = 8 * a ^ 4 + 8 * (4 * a ^ 3) + 8 * (6 * a ^ 2) + 8 * (4 * a) + 8 := by ring
        _ < 7 ^ a + 7 ^ a + 7 ^ a + 7 ^ a + 3 * 7 ^ a := by
          gcongr; apply lt_of_le_of_lt _ ih
          nth_rw 2 [pow_succ']; gcongr
          apply lt_trans _ ih; rw [show 4 = 2+2 by rfl, pow_add]
          gcongr; apply lt_of_lt_of_le (show 6<4^2 by simp)
          gcongr; apply lt_trans _ ih; rw [pow_succ]
          gcongr; apply lt_of_lt_of_le (show 4<4^3 by simp)
          gcongr; apply lt_of_lt_of_le (show 8<3*7^4 by simp)
          gcongr; simp
        _ = _ := by ring
  have lm2 : ∀ c ≥ 1, 8 * c ^ 2 < 9 ^ c := by
    intro c cge; induction c with
    | zero => simp at cge
    | succ c ih =>
      by_cases h : c < 1
      · replace h : c = 0 := by omega
        norm_num [h]
      push_neg at h; specialize ih h; calc
        _ = 8 * c ^ 2 + 2 * (8 * c) + 8 := by ring
        _ < 9 ^ c + 2 * 9 ^ c + 6 * 9 ^ c := by
          gcongr; apply lt_of_le_of_lt _ ih; gcongr
          rw [pow_two]; exact Nat.le_mul_self c
          apply lt_of_lt_of_le (show 8<6*9^1 by simp)
          gcongr; simp
        _ = _ := by ring
  have lm3 : ∀ c ≥ 3, 305 + 8 * c ^ 2 < 9 ^ c := by
    intro c cge; induction c with
    | zero => simp at cge
    | succ c ih =>
      by_cases h : c < 3
      · replace h : c = 2 := by omega
        norm_num [h]
      push_neg at h; specialize ih h; calc
        _ = 305 + 8 * c ^ 2 + 2 * (0 + 8 * c) + 8 := by ring
        _ < 9 ^ c + 2 * 9 ^ c + 6 * 9 ^ c := by
          gcongr; apply lt_of_le_of_lt _ ih
          gcongr; simp; rw [pow_two]; exact Nat.le_mul_self c
          apply lt_of_lt_of_le (show 8<6*9^1 by simp)
          gcongr; simp; omega
        _ = _ := by ring
  constructor
  -- First, we show that $2$ divides $k^4+n^2$ by proving $2$ divides $7^k-3^n$
  · intro hdvd; have auxdvd1 : (2 : ℤ) ∣ k ^ 4 + n ^ 2 := by
      apply dvd_trans _ hdvd
      rw [Int.dvd_iff_emod_eq_zero, ← Int.even_iff, Int.even_sub']
      constructor; all_goals intro; apply Odd.pow; rw [Int.odd_iff]; rfl
  -- Prove that $k$ is even by assuming the contrary that $k$ is odd
    rw [Int.dvd_iff_emod_eq_zero, ← Int.even_iff] at auxdvd1
    by_cases kpar : Odd k
    · rw [Int.even_add'] at auxdvd1
    -- Prove that $n$ is odd
      have npar : Odd n := by
        rw [← Int.odd_coe_nat, ← Int.odd_pow' (show 2≠0 by simp), ← auxdvd1]
        apply Odd.pow; rw [Int.odd_coe_nat]; exact kpar
    -- Prove that $4$ divides $k^4+n^2$ by proving $4$ divides $7^k-3^n$
      have : (4 : ℤ) ∣ k ^ 4 + n ^ 2 := by
        apply dvd_trans _ hdvd; rw [← Int.modEq_zero_iff_dvd]
        apply Int.ModEq.add_right_cancel' (3^n); simp; calc
          _ ≡ (-1) ^ k [ZMOD 4] := by apply Int.ModEq.pow; rfl
          _ ≡ -1 [ZMOD 4] := by rw [Odd.neg_one_pow]; exact kpar
          _ ≡ (-1) ^ n [ZMOD 4] := by rw [Odd.neg_one_pow]; exact npar
          _ ≡ _ [ZMOD 4] := by apply Int.ModEq.pow; rfl
      rw [Int.dvd_iff_emod_eq_zero] at this
    -- Specialize lm to prove $k^4+n^2$ modulo $4$ is $2$, which is a contradiction
      specialize oddsq (k^2) n (show _ by apply Odd.pow; rw [Int.odd_coe_nat]; exact kpar)
      specialize oddsq (show _ by rw [Int.odd_coe_nat]; exact npar); rw [← pow_mul] at oddsq
      linarith only [this, oddsq]
  -- Now we have $k$ is even, prove that $n$ is also even
    rw [Nat.not_odd_iff_even] at kpar; rw [Int.even_add] at auxdvd1
    replace auxdvd1 : Even n := by
      rw [← Int.even_coe_nat, ← Int.even_pow' (show 2≠0 by simp), ← auxdvd1, Int.even_pow']
      rw [Int.even_coe_nat]; exact kpar; simp
  -- Let $k=2*a$ and $n=2 *b$, prove that $b$ is even by showing that $8$ divides $16 *a ^ 4 + 4 *b ^ 2$
    rcases kpar with ⟨a, ha⟩; rcases auxdvd1 with ⟨b, hb⟩; rw [← two_mul] at ha hb
    rw [ha, hb, pow_mul, pow_mul] at hdvd; push_cast at hdvd
    rw [mul_pow, mul_pow] at hdvd; norm_num at hdvd
    obtain ⟨c, hc⟩ : Even b := by
      have : (8 : ℤ) ∣ 16 * a ^ 4 + 4 * b ^ 2 := by
        apply dvd_trans _ hdvd; rw [← Int.modEq_iff_dvd]; calc
        _ ≡ 1 ^ b [ZMOD 8] := by apply Int.ModEq.pow; rfl
        _ ≡ 1 ^ a [ZMOD 8] := by simp
        _ ≡ _ [ZMOD 8] := by apply Int.ModEq.pow; rfl
      rw [dvd_add_right, show (8:ℤ) = 4*2 by simp] at this
      rw [mul_dvd_mul_iff_left, Prime.dvd_pow_iff_dvd] at this
      norm_cast at this; rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
      exact this; exact Int.prime_two
      any_goals simp
      apply dvd_mul_of_dvd_left; norm_num
  -- Rewrite `hdvd` using `sq_sub_sq` and prove that $7^a+9^b$ divides $8*(a^4+c^2)$
    rw [← two_mul] at hc
    rw [hc, show (49:ℤ) = 7^2 by simp, ← pow_mul, pow_mul', pow_mul'] at hdvd
    push_cast at hdvd; rw [mul_pow, ← mul_assoc] at hdvd
    norm_num at hdvd; rw [← mul_add] at hdvd
    rw [sq_sub_sq] at hdvd
    have auxdvd2 : (7 : ℤ) ^ a + 9 ^ c ∣ 8 * (a ^ 4 + c ^ 2) := by
      have : (7 : ℤ) ^ a - 9 ^ c = (7 ^ a - 9 ^ c) / 2 * 2 := by
        rw [Int.ediv_mul_cancel]; rw [← Int.modEq_iff_dvd]; calc
          _ ≡ 1 ^ c [ZMOD 2] := by apply Int.ModEq.pow; rfl
          _ ≡ 1 ^ a [ZMOD 2] := by simp
          _ ≡ _ [ZMOD 2] := by apply Int.ModEq.pow; rfl
      rw [this, ← mul_assoc, mul_comm, show (16:ℤ) = 2*8 by simp] at hdvd
      rw [mul_assoc, mul_dvd_mul_iff_left] at hdvd
      apply dvd_trans _ hdvd; any_goals simp
  -- Prove that $a$ is less than $4$ by assuming the contrary and specialize lm1 and lm2 at $a$ and $c$ respectively
    rw [mul_add] at auxdvd2; norm_cast at auxdvd2
    have alt : a < 4 := by
      by_contra!; specialize lm1 a this; specialize lm2 c (show _ by omega)
      apply Nat.le_of_dvd at auxdvd2; omega; positivity
  -- Split the goal to cases when $a$ is $1$, $2$ or $3$
  -- In each case, we prove $c$ is less or equal to $2$ by assuming the contrary and specialize lm3 to $c$, then use linarith to find a contradiction
    interval_cases a; omega
    · simp_all; have cle : c ≤ 2 := by
        by_contra!; specialize lm3 c (show _ by omega)
        apply Nat.le_of_dvd at auxdvd2
        omega; positivity
      interval_cases c; simp; omega
    · simp_all; have cle : c ≤ 2 := by
        by_contra!; specialize lm3 c (show _ by omega)
        apply Nat.le_of_dvd at auxdvd2
        omega; positivity
      interval_cases c; all_goals omega
    simp_all; have cle : c ≤ 2 := by
      by_contra!; specialize lm3 c (show _ by omega)
      apply Nat.le_of_dvd at auxdvd2
      omega; positivity
    interval_cases c; all_goals omega
-- Conversely, it is straightforward to check that when $k=2$ and $n=4$, the desired division relation holds
  rintro ⟨hk, hn⟩; norm_num [hk, hn]