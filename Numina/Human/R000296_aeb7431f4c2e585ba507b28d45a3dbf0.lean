import Mathlib

/-
  Let  $f$  be a function defined on the positive integers, taking positive integral values, such that
  $f(a)f(b) = f(ab)$  for all positive integers  $a$  and  $b$ ,
  $f(a) < f(b)$  if  $a < b$ ,
  $f(3) \geq 7$ .

  Find the smallest possible value of  $f(3)$ .
-/


theorem number_theory_8849 : (∀ f : ℕ+ → ℕ+, ((∀ a b , (f a) * (f b) = f (a * b)) ∧ (∀ a b , a < b → f a < f b) ∧ f 3 ≥ 7) → f 3 ≥ 9)
    ∧ (∃ f : ℕ+ → ℕ+, ((∀ a b , (f a) * (f b) = f (a * b)) ∧ (∀ a b , a < b → f a < f b) ∧ f 3 ≥ 7) ∧ f 3 = 9) := by
  -- Hypothesis on function f
  let hf (f : ℕ+ → ℕ+) := (∀ a b , (f a) * (f b) = f (a * b)) ∧ (∀ a b , a < b → f a < f b) ∧ f 3 ≥ 7

  -- We first show the lower bound
  have f_lower_bound : (∀ f, hf f → f 3 ≥ 9) := by
    rintro f ⟨hfmul, hfmono, hfge⟩

    -- Conduct case analysis on value of f 2. Starting with f 2 ≥ 2
    have f_2_ge_2 : f 2 ≥ 2 := by
      have h1 : f 1 ≥ 1 := by exact PNat.one_le (f 1)
      have h2 : f 1 < f 2 := by apply hfmono 1 2 ?_; trivial
      calc
        f 2 ≥ (f 1) + 1 := by exact h2
        _ ≥ 2 := by exact PNat.natPred_le_natPred.mp h1

    rcases eq_or_gt_of_le f_2_ge_2 with f_2_eq_2 | f_2_gt_2
    · -- Case 1 : f 2 = 2
      -- Plan:
      --  f 2 = 2 → f 4 = 4
      --  f 3 ≥ 7 → f 4 > 7
      --
      have : (f 4).val = 4 := by
        suffices h : f 4 = 4 from by simp_all only [ge_iff_le, le_refl, PNat.val_ofNat]
        calc
          f 4 = f 2 * f 2 := by rw [hfmul 2 2]; rfl
          _ = 2 * 2 := by rw [f_2_eq_2]
          _ = 4 := rfl
      have : (f 4).val > 7 := by calc
        f 4 > f 3 := by apply hfmono; simp
        _ ≥ 7 := hfge
      linarith

    have f_2_ge_3 : f 2 ≥ 3 := f_2_gt_2
    rcases eq_or_gt_of_le f_2_ge_3 with f_2_eq_3 | f_2_gt_3
    · -- Case 2 : f 2 = 3
      --Plan:
      --  f 2 = 3 → f 16 = 81 → f 15 < 81 → f 30 < 243
      --  f 3 ≥ 7 → f 9 ≥ 49 → f 10 > 49 → f 30 > 343
      --
      have : (f 30).val < 243 := by calc
        f 30 = f 15 * f 2 := by rw [hfmul 15 2]; rfl
        _ = f 15 * 3 := by rw [f_2_eq_3]
        _ < f 16 * 3 := by apply mul_lt_mul_right'; apply hfmono; simp
        _ = f 4 * f 4 * 3 := by simp; rw [hfmul 4 4]; rfl
        _ = f 2 * f 2 * f 2 * f 2 * 3 := by simp; rw [hfmul 2 2, mul_assoc, hfmul 2 2]; rfl
        _ = 3 * 3 * 3 * 3 * 3 := by rw [f_2_eq_3]
        _ = 243 := rfl
      have : (f 30).val > 343 := by calc
        f 30 = f 3 * f 10 := by rw [hfmul 3 10]; rfl
        _ > f 3 * f 9 := by apply (mul_lt_mul_iff_left (f 3)).mpr; apply hfmono; simp
        _ = f 3 * f 3 * f 3 := by rw [mul_assoc, hfmul 3 3]; rfl
        _ ≥ 7 * 7 * 7 := mul_le_mul_three hfge hfge hfge
        _ = 343 := by rfl
      linarith

    -- Case 3 : f 2 ≥ 4. We prove by contradiction
    have f_2_ge_4 : f 2 ≥ 4 := f_2_gt_3
    by_contra! f_3_lt_9
    -- Plan:
    --  f 2 ≥ 4 → f 8 ≥ 64
    --  f 3 < 9 → f 9 ≤ 64
    --
    have : (f 9).val > 64 := by
      suffices h : f 9 > 64 from h
      calc
        f 9 > f 8 := by apply hfmono; simp
        _ = f 4 * f 2 := by rw [hfmul 4 2]; rfl
        _ = f 2 * f 2 * f 2 := by rw [hfmul 2 2]; rfl
        _ ≥ 4 * 4 * 4 := mul_le_mul_three f_2_ge_4 f_2_ge_4 f_2_ge_4
        _ = 64 := rfl
    have : (f 9).val ≤ 64 := by
      suffices h : f 9 ≤ 64 from h
      calc
        f 9 = f 3 * f 3 := by rw [hfmul 3 3]; rfl
        _ ≤ 8 * 8 := by apply mul_le_mul' <;> exact PNat.lt_add_one_iff.mp f_3_lt_9
        _ = 64 := rfl
    linarith

  constructor
  · exact f_lower_bound
  · use fun x ↦ x * x   -- To show the lower bound can be obtained, use square function
    simp_arith
    constructor
    · intros; ring
    intros; apply Left.mul_lt_mul <;> assumption