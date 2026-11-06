import Mathlib

theorem number_theory_5006_1 (a m n : ℕ) (ham : Nat.Coprime a m) (ha : 1 < a) (hn : 0 < n)
    (hm : m = a ^ n - 1) [Fintype (ZMod m)ˣ] [NeZero m] :
    orderOf (ZMod.unitOfCoprime a ham) = n := by
  
  have r2 : m ∣ a ^ n - 1 := by rw [hm]
  have r3 : a = Units.val (ZMod.unitOfCoprime a ham) := rfl
  have r4 : 1 = Units.val (1 : (ZMod m)ˣ) := rfl
  have r5 : (1 : (ZMod m)) = ↑(1 : ℕ) := by simp
  have r6 : 1 ≤ a ^ n := Nat.one_le_pow n a (show 0 < a by linarith)
  rw [← Nat.modEq_iff_dvd', ← ZMod.eq_iff_modEq_nat] at r2
  simp at r2; rw [r3, r4, ← Units.val_pow_eq_pow_val, Units.eq_iff] at r2
  symm at r2
  
  rw [orderOf_eq_iff]; constructor
  · exact r2
  
  intro k hk1 hk2; by_contra h'
  rw [← Units.eq_iff, Units.val_pow_eq_pow_val, ← r3, ← r4, r5] at h'
  symm at h'
  rw [← Nat.cast_pow, ZMod.eq_iff_modEq_nat, Nat.modEq_iff_dvd'] at h'
  apply Nat.le_of_dvd at h'; rw [hm] at h'
  apply (Nat.sub_le_sub_iff_right (Nat.one_le_pow k a (show 0 < a by linarith))).mp at h'
  apply (Nat.pow_le_pow_iff_right ha).mp at h'; linarith
  rw [Nat.sub_pos_iff_lt, Nat.one_lt_pow_iff]; assumption; linarith
  exact (Nat.one_le_pow k a (show 0 < a by linarith)); assumption
  apply Nat.one_le_pow; linarith

theorem number_theory_5006_2 (a m n : ℕ) (ham : Nat.Coprime a m) (ha : 1 < a) (hn : 0 < n)
    (hm : m = a ^ n - 1) [Fintype (ZMod m)ˣ] [NeZero m] :
    n ∣ m.totient := by
  have h1 : orderOf (ZMod.unitOfCoprime a ham) = n := number_theory_5006_1 a m n ham ha hn hm
  have h2 : orderOf (ZMod.unitOfCoprime a ham) ∣ Fintype.card ((ZMod m)ˣ) := by
    apply orderOf_dvd_card
  rw [h1] at h2
  have h3 : Fintype.card ((ZMod m)ˣ) = m.totient := by
    rw [ZMod.card_units_eq_totient]
  rw [h3] at h2
  exact h2