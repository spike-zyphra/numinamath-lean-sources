import Mathlib

/- Example 6 Given $a_{1}=1, a_{2}=2, a_{n+2}=\left\{\begin{array}{l}5 a_{n+1}-3 a_{n}, \text { if } a_{n} a_{n+1} \text { is even } \\ a_{n+1}-a_{n}, \text { if } a_{n} a_{n+1} \text { is odd }\end{array}\right.$, prove: for all positive integers $n, a_{n} \neq 0$ -/
theorem algebra_108263 {a : ℕ → ℤ} (ha0 : a 0 = 1) (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 2) = if Even (a n * a (n + 1)) then 5 * a (n + 1) - 3 * a n else a (n + 1) - a n) :
    ∀ n, a n ≠ 0 := by
  -- we'll prove that a(n) are not zero modulo 4, hence not 0 originally, so define b(n) to be residue in modulo 4
  let b (n : ℕ) := (a n : ZMod 4)
  -- proving b(n) is sufficient
  suffices ∀ n, b n ≠ 0 by
    rintro n
    by_contra h
    specialize this n
    simp [h, b] at this
  -- prove recursion for b corresponding to a's recursion
  have hbn (n : ℕ) : b (n + 2) = if (b n * b (n + 1) = 0 ∨ b n * b (n + 1) = 2)
      then b (n + 1) + b n else b (n + 1) - b n := by
    -- prove that evenness of a(n) * a(n+1) means b(n) * b(n+1) = 0 or 2
    have heven : Even (a n * a (n + 1)) ↔ (b n * b (n + 1) = 0 ∨ b n * b (n + 1) = 2) := by
      simp [b]
      norm_cast
      rw [show (0 : ZMod 4) = ↑(0 : ℤ) by norm_cast, show (2 : ZMod 4) = ↑(2 : ℤ) by norm_cast]
      rw [ZMod.intCast_eq_intCast_iff', ZMod.intCast_eq_intCast_iff', Int.even_iff]
      generalize a n * a (n + 1) = x
      simp only [Nat.cast_ofNat, EuclideanDomain.zero_mod, Int.reduceMod]
      clear * - x
      -- to prove it utlize the fact that (x % 4) % 2 = x % 2
      constructor <;> rintro h
      . have := Int.emod_lt x (show 4 ≠ 0 by norm_num)
        simp at this
        have := Int.emod_nonneg x (show 4 ≠ 0 by norm_num)
        interval_cases h' : (x % 4)
        any_goals simp
        repeat
          rw [← Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ 4 by norm_num), h'] at h
          simp at h
      . rw [← Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ 4 by norm_num)]
        obtain h | h := h
        all_goals rw [h]
        all_goals norm_num
    -- rewrite and do casting to prove the recursion in general
    simp_rw [← heven]
    simp [b]
    rw [han]
    push_cast
    congr
    rw [show (5 : ZMod 4) = 1 by norm_cast, show (3 : ZMod 4) = -1 by norm_cast]
    ring
  -- prove values of b at 0, 1, 2
  have hb0 : b 0 = 1 := by simp [b, ha0]
  have hb1 : b 1 = 2 := by simp [b, ha1]
  have hb2 : b 2 = 3 := by
    rw [hbn]
    simp [hb0, hb1]
    norm_num
  -- prove using induction that b(3k) = 1, b(3k+1) = 2, b(3k+2) = 3
  have hbn' (k : ℕ) : b (3 * k) = 1 ∧ b (3 * k + 1) = 2 ∧ b (3 * k + 2) = 3 := by
    induction' k with m hm
    . simp [hb0, hb1, hb2]
    . have hb0' : b (3 * m + 3) = 1 := by
        rw [hbn, hm.right.left, hm.right.right]
        norm_cast
      have hb1' : b (3 * m + 4) = 2 := by
        rw [hbn, hm.right.right, hb0']
        norm_cast
      have hb2' : b (3 * m + 5) = 3 := by
        rw [hbn, hb0', hb1']
        norm_cast
      ring_nf at hb0' hb1' hb2' ⊢
      simp [hb0', hb1', hb2']
  rintro n
  -- now just write n as 3 * (n/3) + (n % 3) and caseworking on n % 3 and using last fact, we see b(n) = 1, 2 or 3 so not 0.
  rw [← Nat.div_add_mod n 3]
  have := Nat.mod_lt n (show 0 < 3 by norm_num)
  specialize hbn' (n / 3)
  interval_cases (n % 3)
  . rw [add_zero, hbn'.left]
    norm_cast
  . rw [hbn'.right.left]
    norm_cast
  . rw [hbn'.right.right]
    norm_cast