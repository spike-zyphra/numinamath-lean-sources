import Mathlib

theorem number_theory_34410 : {x : Fin 25 | x ^ 3 + 3 * x ^ 2 + x + 3 ≡ 0 [MOD 25]}.ncard = 6 := by
  have h1 : {x : Fin 25 | x ^ 3 + 3 * x ^ 2 + x + 3 ≡ 0 [MOD 25]} = 
    {2, 7, 12, 17, 22, 18} := by
    ext x
    simp [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · -- Assume x^3 + 3x^2 + x + 3 ≡ 0 [MOD 25]; prove x ∈ {2, 7, 12, 17, 22, 18}
      intro h
      fin_cases x <;> simp [Nat.ModEq] at h ⊢ <;> omega
    · -- Assume x ∈ {2, 7, 12, 17, 22, 18}; prove x^3 + 3x^2 + x + 3 ≡ 0 [MOD 25]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 2
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
      · -- x = 7
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
      · -- x = 12
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
      · -- x = 17
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
      · -- x = 22
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
      · -- x = 18
        simp [Nat.ModEq]
        <;> try { native_decide }
        <;> try { norm_num }
        <;> try { native_decide }
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }