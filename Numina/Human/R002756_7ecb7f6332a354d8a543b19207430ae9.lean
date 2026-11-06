import Mathlib

lemma lemma_digits_le_base : ∀ a, ∀ d ∈ Nat.digits 10 a, d ≤ 9 := by
  intro a d h
  suffices d < 10 by omega
  exact Nat.digits_lt_base (by simp) h

-- xs.sum has an upper bound.
lemma lemma_sum_upperbound (xs : List ℕ) (h : ∀ d ∈ xs, d ≤ 9) : xs.sum ≤ 9 * xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp at *
      specialize ih h.right
      ring_nf
      omega

-- If xs.sum = 9 * xs.length, xs must consist of all 9s. This conclusion is expressed in the form of Nat.ofDigits 10 xs.
lemma lemma_number_of_all_9 (xs : List ℕ) (h : ∀ d ∈ xs, d ≤ 9) : xs.sum = 9 * xs.length → Nat.ofDigits 10 xs = 10 ^ xs.length - 1 := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp at *
      obtain ⟨h1, h2⟩ := h
      intro heq
      ring_nf at heq
      have := lemma_sum_upperbound tail h2
      have heq1 : head = 9 := by omega
      have heq2 : tail.sum = 9 * tail.length := by omega
      specialize ih h2 heq2
      rw [Nat.ofDigits_cons, ih, heq1]
      have : 10 ^ tail.length ≥ 1 := by
        apply Left.one_le_pow_of_le
        simp
      ring_nf
      omega

-- If a < 10^9, a's digit sum ≤ 9 * 9. This is obvious.
lemma lemma_sum_upperbound_1 : ∀ a, a < 10 ^ 9 → (Nat.digits 10 a).sum ≤ 81 := by
  intro a h
  have := Nat.le_digits_len_le 10 a (10 ^ 9 - 1) (by omega)
  simp at this
  have := lemma_sum_upperbound (Nat.digits 10 a) (lemma_digits_le_base a)
  omega

-- If 10^9 ≤ a < 1899999999, a's digit sum < 9 * 9
lemma lemma_sum_upperbound_2 : ∀ a, 10 ^ 9 ≤ a → a < 1899999999 → (Nat.digits 10 a).sum < 81 := by
  intros a h1 h2
  -- We divide a into m and n, in such a way that 1899999999 would be divided into 18 and 99999999
  let m := a / 10 ^ 8
  let n := a % 10 ^ 8
  have ha : n + 10 ^ 8 * m = a := by omega
  let k := 8 - (Nat.digits 10 n).length
  have hkn : (Nat.digits 10 n).length + k = 8 := by
    have := Nat.le_digits_len_le 10 n (10 ^ 8 - 1) (by omega)
    simp at this
    simp [k]
    omega
  -- And Nat.digits 10 a can be expressed in terms of Nat.digits 10 m and Nat.digits 10 n.
  have := Nat.digits_append_zeroes_append_digits (b := 10) (k := k) (m := m) (n := n) (by omega) (by omega)
  rw [hkn, ha] at this
  rw [←this]
  simp
  -- And now we have (Nat.digits 10 n).sum + (Nat.digits 10 m).sum = (Nat.digits 10 a).sum

  -- m's digit sum ≤ 9, and the maximum is only taken when m = 18
  -- proved by simple case analysis
  have : (Nat.digits 10 m).sum ≤ 9 ∧ ((Nat.digits 10 m).sum = 9 → m = 18) := by
    have : m ≤ 18 := by omega
    have : 10 ≤ m := by omega
    interval_cases m <;> simp

  -- n's digit sum ≤ 72, and the maximum is only taken when n = 10 ^ 8 - 1
  have : (Nat.digits 10 n).sum ≤ 72 ∧ ((Nat.digits 10 n).sum = 72 → n = 10 ^ 8 - 1) := by
    have digits_le_base_n := lemma_digits_le_base n
    have sum_upperbound_n := lemma_sum_upperbound (Nat.digits 10 n) digits_le_base_n
    constructor
    . -- n's upper bound is given by lemma_sum_upperbound
      have := Nat.le_digits_len_le 10 n (10 ^ 8 - 1) (by omega)
      simp at this
      omega
    . -- and when the maximum value is taken, n must consist of all 9s, thus proved
      intro hsum
      rw [←Nat.ofDigits_digits 10 n]
      have := lemma_number_of_all_9 (Nat.digits 10 n) digits_le_base_n (by omega)
      have hlen : (Nat.digits 10 n).length = 8 := by omega
      simp [hlen] at this
      assumption

  -- Suming these up, we have (Nat.digits 10 n).sum + (Nat.digits 10 m).sum ≤ 81
  by_cases (Nat.digits 10 n).sum + (Nat.digits 10 m).sum = 81
  . -- but when the sum is 81, we'd have a = 1899999999 which is a contradiction.
    have : m = 18 := by omega
    have : n = 10 ^ 8 - 1 := by omega
    have : a = 1899999999 := by omega
    linarith
  omega

/- Find the smallest 10-digit number, the sum of whose digits is not less than that of any smaller number. -/
theorem number_theory_109751 :
    IsLeast {n | n ≥ 1000000000 ∧ ∀ m, m < n → (Nat.digits 10 m).sum ≤ (Nat.digits 10 n).sum} 1899999999 := by
  constructor
  . -- Forall m < 1899999999, m's digit sum is no greater than 1899999999's
    simp
    intro m h
    by_cases 10 ^ 9 ≤ m
    . have := lemma_sum_upperbound_2 m (by omega) (by omega)
      omega
    . exact lemma_sum_upperbound_1 m (by omega)
  . -- And 1899999999 is the smallest such number
    intro m h
    simp at h
    obtain ⟨h1, h2⟩ := h
    by_contra!
    -- suppose it's not, there exists m ∈ [10^9, 1899999999) meeting above condition
    -- but the digit sum of m is at most 80, while (10^9-1)'s is 81
    have := lemma_sum_upperbound_2 m (by omega) (by omega)
    specialize h2 (10 ^ 9 - 1) (by omega)
    simp at h2
    linarith
