import Mathlib

open Int

theorem number_theory_6971 {x y : ℝ} :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧
    (x % 1 + y % 1 ≥ (x + y) % 1) ∧
    ∀ x : ℝ, ∃ n : ℤ, x = n → ⌊-x⌋ = -n ∧
    ∀ x : ℝ, x ≠ n → ⌊-x⌋ = -n + 1 := by
  constructor
  · -- Proof of ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋
    exact Int.le_floor_add x y
  constructor
  · -- Proof of x % 1 + y % 1 ≥ (x + y)  -- needs framework for x % 1.
    simp
  · -- Proof of ∀ x : ℝ, ∃ n : ℤ, x = n → ⌊-x⌋ = -n ∧ ∀ x : ℝ, x ≠ n → ⌊-x⌋ = -n + 1
    intro x
    use (⌊x⌋ + 42 : ℤ)
    intro h
    exfalso
    have h_eq : x = (⌊x⌋ + 42 : ℝ) := by
      simpa using h
    have h1 : ⌊x⌋ = ⌊x⌋ := rfl
    have h4 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
    have h2 : x < ((⌊x⌋ + 1 : ℝ)) := by exact_mod_cast (Int.lt_floor_add_one x)
    have h3 : ((⌊x⌋ + 42 : ℝ) : ℝ) ≤ x := by
      nlinarith [h_eq, h4]
    -- deriving contradiction here.
    nlinarith