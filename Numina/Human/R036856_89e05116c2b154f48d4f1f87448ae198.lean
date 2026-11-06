import Mathlib

theorem number_theory_222631 (p : ℕ) (hp : p > 0) : 84 ∣ (4^(2*p) - 3^(2*p) - 7 : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 1 := by
    match p with
    | 0 => simp at hp
    | Nat.succ k => exact ⟨k, rfl⟩
  clear hp
  simp [mul_add, pow_succ]
  rw [pow_mul,
      pow_mul,
      show (84 : ℤ) = Multiset.lcm {3, 4, 7} by native_decide,
      Multiset.lcm_dvd]
  ring_nf
  simp
  refine ⟨?_, ?_, ?_⟩ <;> rw [← Int.modEq_zero_iff_dvd]
  . calc
      _ ≡ -1 - 0 ^ k * 0 + 1 ^ k * 1 [ZMOD 3] := by gcongr <;> rfl
      _ ≡ 0 [ZMOD 3] := by simp
  . calc
      _ ≡ 1 - 1 ^ k * 1 + 0 ^ k * 0 [ZMOD 4] := by gcongr <;> rfl
      _ ≡ 0 [ZMOD 4] := by simp
  . calc
      _ ≡ 0 - 2 ^ k * 2 + 2 ^ k * 2 [ZMOD 7] := by gcongr <;> rfl
      _ ≡ 0 [ZMOD 7] := by simp
