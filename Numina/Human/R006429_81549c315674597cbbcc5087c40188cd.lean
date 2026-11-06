import Mathlib

/-!
Let D be a positive integer such that gcd(3, D)=1.
Let f(x)=3x+2.
Prove that there exists a natural number m such that f^[100](m) is divisible by D.
-/

-- The main theorem, refactored with ZMod
theorem exists_m_divisible_by_D
    (D : ℕ) (hD_pos : D > 0) (h_gcd : Nat.gcd 3 D = 1) :
    let f := fun (x : ℤ) => 3 * x + 2;
    ∃ m : ℕ, m > 0 ∧ (f^[100] m) % D = 0 := by

  let f := fun (x : ℤ) => 3 * x + 2

  let rec f_iter: ℕ → ℤ → ℤ := fun (n : ℕ) (x : ℤ) =>
    match n with
    | 0   => x
    | n+1 => f (f_iter n x)

  -- Prove the closed-form formula for f_iter n x
  have f_pow_formula : (f : ℤ → ℤ) → (h_f : f = fun x => 3 * x + 2) → (n : ℕ) → (x : ℤ) → f^[n] x = 3^n * x + 3^n - 1 := by
    intro f h_f n x
    induction n with
    | zero =>
      -- Base case: n = 0
      calc f^[0] x
        _ = x                               := by rw [Function.iterate_zero_apply]
        _ = 1 * x + 0                       := by rw [one_mul, add_zero]
        _ = 3^0 * x + 3^0 - 1               := by omega
    | succ n ih =>
      -- Inductive step for n + 1
      calc f^[n + 1] x
        _ = f (f^[n] x)                     := by rw [Function.iterate_succ_apply']
        _ = f (3^n * x + 3^n - 1)           := by rw [ih]
        _ = 3 * (3^n * x + 3^n - 1) + 2     := by rw [h_f]
        _ = 3^(n+1) * x + 3^(n+1) - 1       := by ring

  -- We work in the ring `ZMod D`. The goal is to find a positive `m : ℕ`
  -- such that `(f^[100] (m : ℤ) : ZMod D) = 0`.
  -- Using the formula, this is `(↑(3^100) * ↑m + ↑(3^100) - 1 : ZMod D) = 0`.

  let a : ZMod D := ↑(3^100)

  -- We show that `a` is a unit. `IsUnit (n : ZMod D)` is equivalent to `Nat.gcd n.val D = 1`.
  -- Since `Nat.gcd 3 D = 1`, `(3 : ZMod D)` is a unit. The power of a unit is a unit.
  have h_a_isUnit : IsUnit a := by
    -- `(3 : ZMod D)` is a unit because `Nat.gcd 3 D = 1`.
    have h_unit_3 : IsUnit (3 : ZMod D) := (ZMod.unitOfCoprime 3 h_gcd).isUnit
    -- The power of a unit is also a unit.
    exact IsUnit.pow 100 h_unit_3

  -- The equation to solve is `a * ↑m + (a - 1) = 0`, which is `a * ↑m = 1 - a`.
  -- Since `a` is a unit, we can find a unique solution for `↑m` in `ZMod D`.
  let m_zmod : ZMod D := h_a_isUnit.unit⁻¹ * (1 - a)

  -- Let `m₀` be the canonical representative of `m_zmod` in `ℕ`, where `0 ≤ m₀ < D`.
  let m₀ := ZMod.val m_zmod

  -- We need to find a *positive* natural number `m`. We consider two cases for `m₀`.
  by_cases h_m₀_zero : m₀ = 0
  · -- Case 1: `m₀ = 0`. This implies `m_zmod = 0`.
    -- In this case, `1 - a = 0`, so `a = 1`.
    -- This means `3^100 ≡ 1 (mod D)`, so `f^[100] 0` is divisible by `D`.
    -- We need a positive `m`. Let's use `m = D`.
    use D
    constructor
    · -- `D > 0` is given by the hypothesis `hD_pos`.
      exact hD_pos
    · -- Show `f^[100] D` is divisible by `D`.
      -- We show that the result is 0 in `ZMod D`.
      --rw [← ZMod.int_cast_eq_zero_iff_dvd]
      have h_a_eq_one : a = 1 := by
        -- `m₀=0` means `m_zmod=0`. `m_zmod = u⁻¹ * (1-a)`, so `1-a=0`.
        rw [ZMod.val_eq_zero] at h_m₀_zero
        have h_a: 1 - a = 0 := by exact (Units.mul_right_eq_zero h_a_isUnit.unit⁻¹).mp h_m₀_zero
        have h_a': 1 = a := by
          calc
            1 = 1 - a + a := by ring
            _ = 0 + a := by rw [h_a]
            _ = a := by rw [zero_add]
        exact h_a'.symm

      have : (f^[100] D : ZMod D) = 0 := by
        calc (f^[100] D : ZMod D)
          _ = ↑(f^[100] D : ℤ) := by rfl
          _ = ↑((3^100 : ℤ) * D + (3^100 : ℤ) - 1) := by rw [f_pow_formula f rfl]
          _ = ↑(3^100 : ℤ) * ↑D + ↑(3^100 : ℤ) - 1 := by simp [Int.cast_add, Int.cast_sub, Int.cast_mul]
          _ = a * ↑D + ↑a - 1 := by
            simp only [a]
            have : ↑((3: ℤ) ^ 100)= (3 : ZMod D) ^ 100 := by norm_cast
            rw [this]
          _ = a * (D : ZMod D) + a - 1       := by simp only [a]
          _ = a * 0 + a - 1                  := by
            congr
            exact ZMod.natCast_self D
          _ = a - 1                          := by ring
          _ = 1 - 1                          := by rw [h_a_eq_one]
          _ = 0                              := by ring

      have : f^[100] D % D = 0 := by
        have h1:= (ZMod.intCast_zmod_eq_zero_iff_dvd (f^[100] D) D).mp this
        exact Int.emod_eq_zero_of_dvd h1

      exact this

  · -- Case 2: `m₀ ≠ 0`. Then `m₀` is a positive natural number.
    use m₀
    constructor
    · -- We know `m₀ ≠ 0` and `m₀` is a natural number, so `m₀ > 0`.
      exact Nat.pos_of_ne_zero h_m₀_zero
    · -- Show that `m₀` is a valid solution.
      -- We show that the result is 0 in `ZMod D`.
      -- rw [← ZMod.int_cast_zmod_eq_zero_iff_dvd]
      have : (f^[100] (m₀ : ℤ) : ZMod D) = 0 := by
        calc (f^[100] (m₀ : ℤ) : ZMod D)
          _ = ↑((3^100 : ℤ) * m₀ + (3^100 : ℤ) - 1) := by rw [f_pow_formula f rfl]
          _ = ↑(3^100 : ℤ) * ↑m₀ + ↑(3^100 : ℤ) - 1 := by simp [Int.cast_add, Int.cast_sub, Int.cast_mul]
          _ = a * ↑m₀ + ↑a - 1 := by
            simp only [a]
            have : ↑((3: ℤ) ^ 100)= (3 : ZMod D) ^ 100 := by norm_cast
            rw [this]
          _ = a * (m₀ : ZMod D) + a - 1       := by simp only [a]
          _ = a * m_zmod + a - 1            := by
            congr
            rw [show m₀ = m_zmod.val by rfl]
            have : NeZero D := NeZero.of_gt hD_pos
            exact ZMod.natCast_zmod_val m_zmod
          _ = a * (↑h_a_isUnit.unit⁻¹ * (1 - a)) + a - 1 := by simp [m_zmod]
          _ = (a * ↑h_a_isUnit.unit⁻¹) * (1 - a) + a - 1 := by rw [mul_assoc]
          _ = 1 * (1 - a) + a - 1           := by
            congr
            exact IsUnit.mul_val_inv h_a_isUnit
          _ = 0                             := by ring

      have : f^[100] (m₀ : ℤ) % D = 0 := by
        have h1:= (ZMod.intCast_zmod_eq_zero_iff_dvd (f^[100] (m₀ : ℤ)) D).mp this
        exact Int.emod_eq_zero_of_dvd h1

      exact this
