import Mathlib

lemma l_pow_right_inj (ha : 2 ≤ a) : a ^ m = a ^ n ↔ m = n :=
  (Nat.pow_right_injective ha).eq_iff

lemma l_pow_left_inj {a b n : Nat} (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  match Nat.lt_trichotomy a b with
  | Or.inl hab => exact False.elim (absurd h (ne_of_lt (Nat.pow_lt_pow_left hab hn)))
  | Or.inr (Or.inl hab) => exact hab
  | Or.inr (Or.inr hab) => exact False.elim (absurd h (Nat.ne_of_lt' (Nat.pow_lt_pow_left hab hn)))


-- Use this to show the inequality.
lemma lemma_1 (m : ℕ) (mh : m ≥ 4) :
  2 ^ (m - 1) > m + 1 :=
by
  repeat
    rcases m with (_| m)
    simp at mh
  simp
  have : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by rfl
  rw [this] at *
  clear * -
  induction m with
  | zero => simp
  | succ m ih =>
    simp at *
    ring_nf at *
    omega

theorem number_theory_640612 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0
      ∧ a ^ b * b ^ c = c ^ a
      ∧ b = c
      ∧ ∃ k , k = b
      ∧ ∃ m , a = k^m
      } =
    {(1, 1, 1), (8, 2, 2), (9, 3, 3)} :=
by
  ext x
  simp
  constructor; swap
  . -- try each answear.
    rintro (h|h|h)
    all_goals
      rcases x with ⟨a,b,c⟩
      simp at h ⊢
      rcases h with ⟨h1, h2, h3⟩
      subst h1 h2 h3
      simp
    use 3 ; simp
    use 2 ; simp
  . -- main part.
    intro H
    rcases x with ⟨a, b, c⟩
    simp at H ⊢
    rcases H with
      ⟨apos, bpos, cpos, H, bc, ⟨m, mh⟩⟩
    subst bc mh
    simp at *
    have : b ^ (m*b+b) = b ^ b^m := by
      conv =>
        lhs
        rw [pow_add, pow_mul]
      assumption
    rcases em (b = 1) with (b1|_)
    . subst b1
      simp at *
    have : m*b + b = b ^ m := by
      apply (l_pow_right_inj ?_).mp
      exact this
      omega
    have : b * (m + 1) = b^m := by linarith
    rcases em (m = 0) with (m0|_)
    . subst m0
      simp at *
      assumption
    have mpos : m > 0 := by omega
    have : m + 1 = b ^ (m - 1) := by
      qify at this ⊢
      have : (b ^ (m - 1) : ℚ) = b ^ m / b := by
        field_simp
        conv =>
          lhs; rhs
          rw [show (b : ℚ) = b ^ 1 by linarith]
        rw [←pow_add, Nat.sub_add_cancel]
        omega
      rw [this]
      field_simp
      linarith
    rcases em (m < 4) with (h | h)
    . interval_cases m
      . simp at *
      . simp at *
        subst this
        simp
      . simp at *
        have : b = 2 := by
          rw [show 4 = 2^2 by simp] at this
          apply (l_pow_left_inj (by simp)).mp at this
          tauto
        subst this
        simp
    . -- Here we use the lemma
      have := lemma_1 m ?_
      have : b ^ (m-1) ≥ 2 ^ (m -1) := by
        refine Nat.pow_le_pow_left ?_ (m - 1)
        omega
      omega
      omega
