import Mathlib

theorem number_theory_22953 : {n : ℕ | n < 18632 ∧ n ≡ 23 [MOD 37]}.encard = 503 := by
  have h1 : {n : ℕ | n < 18632 ∧ n ≡ 23 [MOD 37]} = Finset.filter (λ n => n ≡ 23 [MOD 37]) (Finset.Iio (18632 : ℕ)) := by
    ext n
    simp [Nat.ModEq]
    <;> aesop
    <;> norm_num
    <;> all_goals omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Iio]
  <;> try { native_decide }
  <;> try { omega }