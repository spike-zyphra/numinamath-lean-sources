import Mathlib

theorem number_theory_178374 : IsSquare (Nat.ofDigits 10 (6 :: List.replicate n 5
    ++ List.replicate (n + 1) 1)) := by
  have auxdvd : ∀ b > 1, ∀ k, (b - 1) ∣ b ^ k - 1 := by
    intro b hb k; rw [← Nat.modEq_iff_dvd']; calc
      _ ≡ 1 ^ k [MOD (b-1)] := by rw [one_pow]
      _ ≡ _ [MOD b-1] := by
        apply Nat.ModEq.pow; calc
          _ ≡ 0 + 1 [MOD b-1] := by rw [zero_add]
          _ ≡ (b - 1) + 1 [MOD b-1] := by apply Nat.ModEq.add; simp [Nat.ModEq]; rfl
          _ ≡ _ [MOD b-1] := by rw [Nat.sub_add_cancel]; omega
    apply Nat.one_le_pow; omega
  have auxdig : ∀ b > 1, ∀ k, ∀ r < b, Nat.ofDigits b (List.replicate k r) = r * ((b ^ k - 1) / (b - 1)) := by
    intro b hb k; have : (b : ℚ) - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; norm_cast at h; omega
    induction k with
    | zero => simp
    | succ k ih =>
      intro r hr; rw [List.replicate_succ, Nat.ofDigits_cons, ih]; qify
      rw [Int.cast_div, Int.cast_div, Nat.cast_sub, Nat.cast_sub]; push_cast
      field_simp; ring; any_goals omega
      apply Nat.one_le_pow; omega
      any_goals norm_cast; apply auxdvd; omega
      any_goals simp; intro h; rw [Nat.sub_eq_zero_iff_le] at h; omega
  use Nat.ofDigits 10 (4 :: List.replicate n 3)
  rw [← pow_two, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_cons]
  rw [auxdig, auxdig, auxdig]; simp; qify
  repeat rw [Int.cast_div]
  push_cast; repeat rw [Nat.cast_sub]
  push_cast; field_simp; ring; any_goals simp
  any_goals apply Nat.one_le_pow; simp
  · specialize auxdvd 10; norm_num at auxdvd
    specialize auxdvd (n+1); zify at auxdvd
    rw [Nat.cast_sub] at auxdvd; push_cast at auxdvd
    exact auxdvd; apply Nat.one_le_pow; simp
  specialize auxdvd 10; norm_num at auxdvd
  specialize auxdvd n; zify at auxdvd
  rw [Nat.cast_sub] at auxdvd; push_cast at auxdvd
  exact auxdvd; apply Nat.one_le_pow; simp