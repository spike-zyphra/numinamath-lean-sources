import Mathlib

/- How many positive perfect squares less than 2023 are divisible by 5?
(A) 8
(B) 9
(C) 10
(D) 11
(E) 12 -/

theorem number_theory_94402 : Set.ncard {x : ℕ | 0 < x^2 ∧ x^2 < 2023 ∧ 5 ∣ x^2} = 8 := by
  -- we will prove that such x are 5 * y, so define f to show injection (hence bijection)
  let f (n: ℕ) : ℕ := 5 * n
  -- prove f is injective
  have finj : Function.Injective f := by
    intro a b hf
    simp [f, Function.Injective] at hf
    assumption
  -- now prove target set = f([1, 8])
  have : {x | 0 < x ^ 2 ∧ x ^ 2 < 2023 ∧ 5 ∣ x ^ 2} = f '' Set.Icc 1 8 := by
    ext x
    constructor
    -- when x in target set then there is y s.t. y in [1, 8] and f(y) = x, to do that prove 5 divides x so 5 * y = x exists. use that y
    . rintro ⟨hx₁, hx₂, hx₃⟩
      have h5x: 5 ∣ x := by
        apply Nat.Prime.dvd_of_dvd_pow
        norm_num
        assumption
      have hxpos : 0 < x := by exact Nat.pos_of_mul_pos_left hx₁
      have h5x' : 5 ≤ x := by refine Nat.le_of_dvd hxpos h5x
      have ⟨y, hy⟩ := h5x
      use y
      constructor
      any_goals constructor
      -- prove 0 < x^2, x^2 < 2023, 5 | x^2
      . omega
      . have : x^2 < 45^2 := by linarith
        have : x < 5 * 9 := by exact lt_of_pow_lt_pow_left' 2 this
        omega
      . dsimp [f]
        rw [hy]
    -- now prove x in f([1, 8]) implies x in target set
    . rintro ⟨y, ⟨hy₁, hy₂⟩, hf⟩
      dsimp [f] at hf
      constructor
      any_goals constructor
      -- prove 0 < x^2
      . apply Nat.pos_pow_of_pos 2
        omega
      -- prove x^2 < 2023
      . suffices h: x^2 ≤ 40^2 from by linarith
        refine Nat.pow_le_pow_left ?_ _
        omega
      -- prove 5 | x^2
      . rw [← hf]
        ring_nf
        omega
  -- finally using last fact prove cardinality is same as [1, 8]'s which is 8
  have : {x : ℕ | 0 < x^2 ∧ x^2 < 2023 ∧ 5 ∣ x^2}.ncard = 8 := by
    calc
      {x : ℕ | 0 < x^2 ∧ x^2 < 2023 ∧ 5 ∣ x^2}.ncard = (f '' (Set.Icc 1 8)).ncard := by congr
      _ = (Set.Icc 1 8).ncard := by exact Set.ncard_image_of_injective _ finj
      _ = Nat.card (Set.Icc 1 8) := by rw[Set.Nat.card_coe_set_eq]
      _ = 8 := by simp
  assumption