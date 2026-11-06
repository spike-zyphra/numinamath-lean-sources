import Mathlib

abbrev p (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 9

-- We break [100000, 999999].filter p into two equal-size parts.
lemma lemma_destruct_into_half :
    (Finset.Icc 100000 999999).filter p =
    (Finset.Icc 100000 499999).filter p ∪
    (Finset.Icc 500000 899999).filter p := by
  -- First we show that [100000, 999999] is the union of the two
  have : Finset.Icc 100000 999999 =
        Finset.Icc 100000 499999 ∪
        Finset.Icc 500000 999999 := by
    apply Finset.ext
    simp
    omega
  rw [this]
  -- Then, we show that there is no number in [900000, 999999].filter p
  have : (Finset.Icc 500000 899999).filter p = (Finset.Icc 500000 999999).filter p := by
    apply Finset.ext
    simp
    intro n hp hl
    constructor <;> intro ha
    . omega
    . by_contra hl
      simp at hl
      -- Because any number in [900000, 999999] starts with 9
      have ⟨a, b, c, d, e, h1⟩ : ∃ a b c d e, Nat.digits 10 n = [a, b, c, d, e, 9] := by
        iterate 6 (
          rw [Nat.digits_def' (by simp) (by omega)]
          simp
          try constructor; omega)
        have hn1 : n / 10 / 10 / 10 / 10 / 10 / 10 = 0 := by omega
        simp [hn1]
      specialize hp 9 (by simp [h1])
      omega
  rw [this]
  apply Finset.filter_union

-- We show that if n doesn't contain 0 and 9 in its digits, then so is 999999 - n.
lemma lemma_999999_minus_n (n : ℕ) (h : n ∈ Finset.Icc 100000 899999) :
    (∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 9) →
    (∀ d ∈ Nat.digits 10 (999999 - n), d ≠ 0 ∧ d ≠ 9) := by
  intro h1 d hd
  simp at h
  let m := 999999 - n
  have h2 : Nat.digits 10 m = List.map (fun x => 9 - x) (Nat.digits 10 n) := by
    have hn : Nat.digits 10 n = [n % 10, n / 10 % 10, n / 100 % 10, n / 1000 % 10, n / 10000 % 10, n / 100000 % 10] := ?hn
    have hm : Nat.digits 10 m = [m % 10, m / 10 % 10, m / 100 % 10, m / 1000 % 10, m / 10000 % 10, m / 100000 % 10] := ?hm
    case hn|hm =>
      iterate 6 (
        rw [Nat.digits_def' (by simp) (by omega)]
        simp
        try constructor; omega)
      have hn1 : n / 10 / 10 / 10 / 10 / 10 / 10 = 0 := by omega
      have hm1 : m / 10 / 10 / 10 / 10 / 10 / 10 = 0 := by omega
      simp [hn1, hm1]
    simp [hn, hm]
    omega
  simp [h2] at hd
  obtain ⟨d', hd', h3⟩ := hd
  specialize h1 d' hd'
  have := Nat.digits_lt_base (by omega) hd'
  omega

-- We transform the sum on [500000, 899999].filter p onto [100000, 499999].filter p.
lemma lemma_mirror_a_half :
    ∑ n ∈ (Finset.Icc 500000 899999) with p n, (n : ℤ) =
    ∑ n ∈ (Finset.Icc 100000 499999) with p n, (999999 - (n : ℤ)) := by
  apply Finset.sum_bij_ne_zero (fun n _ _ => 999999 - n)
  . intros n h _
    simp at h
    obtain ⟨⟨hl, ha⟩, hp⟩ := h
    simp
    constructor
    . omega
    . apply lemma_999999_minus_n _ (by simp; omega)
      assumption
  . intros n1 h1 _ n2 h2 _
    simp at h1 h2
    omega
  . intros n h _
    simp at h
    obtain ⟨⟨hl, ha⟩, hp⟩ := h
    use (999999 - n)
    simp
    repeat any_goals constructor
    all_goals try omega
    apply lemma_999999_minus_n _ (by simp; omega)
    assumption
  . intros n h _
    simp at h
    omega

-- We simplify the body in the big sum.
lemma lemma_sum_up :
    ∑ x ∈ (Finset.Icc 100000 499999).filter p, ((x : ℤ) + (999999 - (x : ℤ))) =
    ∑ _ ∈ (Finset.Icc 100000 499999).filter p, 999999 := by
  apply Finset.sum_congr <;> simp

lemma disjoint : Disjoint
    (Finset.filter p (Finset.Icc 100000 499999))
    (Finset.filter p (Finset.Icc 500000 899999)) := by
  simp [Disjoint]
  intros xs h1 h2
  simp [Subset] at h1 h2
  ext a
  constructor <;> intro h
  . specialize h1 h
    specialize h2 h
    linarith
  . simp at h

/- Prove that the sum of 6-digit numbers, not containing the digits 0 and 9 in their decimal representation, is divisible by 37. -/
theorem number_theory_191759 :
    ∑ n in (Finset.Icc 100000 999999).filter (fun n => ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 9), n ≡ 0 [ZMOD 37] := by
  -- use conv to avoid (deep) kernel recursion
  conv =>
    lhs
    rw [lemma_destruct_into_half, Finset.sum_union disjoint]
    rhs
    rw [lemma_mirror_a_half]
  rw [←Finset.sum_add_distrib, lemma_sum_up]
  simp [Int.ModEq]
  omega
