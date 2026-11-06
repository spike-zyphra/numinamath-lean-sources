import Mathlib

/- 5.9 The sequence $101, 104, 116, \cdots$ has the general term $a_{n}=100+n^{2}$, where $n=1$, $2, 3, \cdots$. For each $n$, let $d_{n}$ denote the greatest common divisor of $a_{n}$ and $a_{n+1}$. Find the maximum value of $d_{n}$. Here $n$ takes all positive integers.
(3rd American Invitational Mathematics Examination, 1985) -/
theorem number_theory_264578 {a : ℕ → ℕ} {d : ℕ → ℕ}
    (ha : ∀ n > 0, a n = 100 + n^2)
    (hd : ∀ n > 0, d n = (a n).gcd (a (n + 1))):
    IsGreatest {d n | n > 0} 401 := by
  -- Prove a more general statement:
  -- define b x n = x + n ^ 2 and show that
  -- the maximum value of gcd (b x n) (b x (n + 1)) is 4 * x + 1
  set b : ℕ → ℕ → ℕ := fun x n => x + n ^ 2
  suffices h : ∀ x > 0, IsGreatest {(b x n).gcd (b x (n + 1)) | n > 0} (4 * x + 1) by
    -- a n = b 100 n for all n > 0 and the result follows from the general statement
    have eq : {d n | n > 0} = {(b 100 n).gcd (b 100 (n + 1)) | n > 0} := by
      ext n
      simp only [gt_iff_lt, Set.mem_setOf_eq, b]
      constructor
      · intro ⟨i, hi, hn⟩
        use i, hi
        simp [hd _ hi, ha _ hi, ha (i + 1) (by omega)] at hn
        exact hn
      · intro ⟨i, hi, hn⟩
        use i, hi
        simp [hd _ hi, ha _ hi, ha (i + 1) (by omega)]
        exact hn
    simp [eq, h 100]
  intro x hx
  simp only [IsGreatest, gt_iff_lt, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  -- first, show that there exists n > 0 such that gcd (b x n) (b x (n + 1)) = 4 * x + 1
  -- use n = 2 * x > 0
  · use 2 * x, by omega
    -- we have b x (2 * x) = x * (4 * x + 1) and b x (2 * x + 1) = (x + 1) * (4 * x + 1)
    simp [b, show x + (2 * x) ^ 2 = x * (4 * x + 1) by ring, show x + (2 * x + 1) ^ 2 = (x + 1) * (4 * x + 1) by ring]
    -- so gcd (b x (2 * x)) (b x (2 * x + 1)) = (4 * x + 1) * gcd x (x + 1)
    rw [Nat.gcd_mul_right]
    -- x and x + 1 are coprime so gcd x (x + 1) = 1
    suffices hx : x.Coprime (x + 1) by rw [hx.gcd_eq_one, one_mul]
    simp_all only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_self, Nat.coprime_self_add_right,
      Nat.coprime_one_right_eq_true]
  -- now prove that d = gcd (b x n) (b x (n + 1)) ≤ 4 * x + 1 for all n > 0
  intro n hn
  set d := (b x n).gcd (b x (n + 1))
  -- we will show that d divides 4 * x + 1
  apply Nat.le_of_dvd (by omega)
  -- show that d divides 2 * n + 1
  have h1 : d ∣ 2 * n + 1 := by
    zify
    -- we have 2 * n + 1 = b x (n + 1) - b x n
    rw [show 2 * (n : ℤ) + 1 = b x (n + 1) - b x n by simp [b]; ring]
    -- d divides b x (n + 1) and d divides b x n so b divides their difference
    apply Int.dvd_sub <;> norm_cast <;> dsimp [d]
    exact Nat.gcd_dvd_right _ _
    exact Nat.gcd_dvd_left _ _
  -- show that d divides 2 * x - n
  have h2 : (d : ℤ) ∣ 2 * x - n := by
    -- we have 2 * x - n = 2 * b x n - n * (2 * n + 1)
    rw [show 2 * (x : ℤ) - n = 2 * b x n - n * (2 * n + 1) by simp [b]; ring]
    -- it is enough to show that d divides 2 * b x n and d divides n * (2 * n + 1)
    apply Int.dvd_sub <;> norm_cast
    -- d divides 2 * b x n because d divides b x n
    · trans b x n
      exact Nat.gcd_dvd_left _ _
      exact Nat.dvd_mul_left (b x n) 2
    -- we proved that d divides 2 * n + 1 so d divides n * (2 * n + 1)
    · have ⟨k, hk⟩ := h1
      use n * k
      rw [hk, Nat.mul_left_comm]
  zify at h1 ⊢
  -- we have 4 * x + 1 = 2 * (2 * x - n) + (2 * n + 1)
  rw [show 4 * (x : ℤ) + 1 = 2 * (2 * x - n) + (2 * n + 1) by ring]
  -- it is left to show that d divides 2 * (2 * x - n) and d divides 2 * n + 1
  -- we proved that d divides 2 * n + 1
  apply Int.dvd_add _ h1
  -- we proved that d divides 2 * x - n so d divides 2 * (2 * x - n)
  have ⟨k, hk⟩ := h2
  use 2 * k
  rw [hk, Int.mul_left_comm]