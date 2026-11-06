import Mathlib

abbrev isPrimitiveRoot (n : ℕ) (k : ZMod n) : Prop :=
  ∀ x : ZMod n, x ≠ 0 → ∃ m : ℕ, k ^ m = x

theorem number_theory_6543 : isPrimitiveRoot 41 7 := by
  intro x hx
  have hne : x ≠ 0 := hx
  have h2 : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨
    x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 16 ∨ 
    x = 17 ∨ x = 18 ∨ x = 19 ∨ x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 23 ∨ x = 24 ∨
    x = 25 ∨ x = 26 ∨ x = 27 ∨ x = 28 ∨ x = 29 ∨ x = 30 ∨ x = 31 ∨ x = 32 ∨
    x = 33 ∨ x = 34 ∨ x = 35 ∨ x = 36 ∨ x = 37 ∨ x = 38 ∨ x = 39 ∨ x = 40 := by
    have hne : x ≠ 0 := hx
    fin_cases x <;> simp [ZMod] at *
    <;> tauto
  rcases h2 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | 
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | 
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | 
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)  
  · -- x = 1
    use 0
    native_decide
  · -- x = 2
    use 14
    native_decide
  · -- x = 3
    use 25
    native_decide
  · -- x = 4
    use 28
    native_decide
  · -- x = 5
    use 18
    native_decide
  · -- x = 6
    use 39
    native_decide
  · -- x = 7
    use 1
    native_decide
  · -- x = 8
    use 2
    native_decide
  · -- x = 9
    use 10
    native_decide
  · -- x = 10
    use 32
    native_decide
  · -- x = 11
    use 37
    native_decide
  · -- x = 12
    use 13
    native_decide
  · -- x = 13
    use 9
    native_decide
  · -- x = 14
    use 15
    native_decide
  · -- x = 15
    use 3
    native_decide
  · -- x = 16
    use 16
    native_decide
  · -- x = 17
    use 7
    native_decide
  · -- x = 18
    use 24
    native_decide
  · -- x = 19
    use 31
    native_decide
  · -- x = 20
    use 6
    native_decide
  · -- x = 21
    use 26
    native_decide
  · -- x = 22
    use 11
    native_decide
  · -- x = 23
    use 4
    native_decide
  · -- x = 24
    use 27
    native_decide
  · -- x = 25
    use 36
    native_decide
  · -- x = 26
    use 23
    native_decide
  · -- x = 27
    use 35
    native_decide
  · -- x = 28
    use 29
    native_decide
  · -- x = 29
    use 33
    native_decide
  · -- x = 30
    use 17
    native_decide
  · -- x = 31
    use 12
    native_decide
  · -- x = 32
    use 30
    native_decide
  · -- x = 33
    use 22
    native_decide
  · -- x = 34
    use 21
    native_decide
  · -- x = 35
    use 19
    native_decide
  · -- x = 36
    use 38
    native_decide
  · -- x = 37
    use 8
    native_decide
  · -- x = 38
    use 5
    native_decide
  · -- x = 39
    use 34
    native_decide
  · -- x = 40
    use 20
    native_decide