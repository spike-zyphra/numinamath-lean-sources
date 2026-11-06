import Mathlib
theorem algebra_609640 : {a : ℝ | ∃ f : ℝ → ℝ, (∀ x y : ℝ, f x * f y = f (x - y)) ∧ f 2017 = a} = {0, 1} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Assume exists f s.t. ∀ x y, f x * f y = f (x - y) and f 2017 = a
    rintro ⟨f, hf, h⟩
    have h1 : f 0 * f 0 = f (0 - 0) := hf 0 0
    -- prove that f(0) = 0 or f(0) = 1
    have h2 : f 0 = 0 ∨ f 0 = 1 := by
      simp at h1
      have : f 0 * (f 0 - 1) = 0 := by linarith
      cases (mul_eq_zero.mp this) with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        linarith
    cases h2 with
    | inl h0 =>
      have h00 : f 2017 * f 2017 = f (2017 - 2017) := hf 2017 2017
      have h01 : f (2017 - 2017) = f 0 := by 
        ring_nf 
      rw [h01, h0] at h00
      have h02 : f 2017 = 0 := by 
        nlinarith 
      have ha : a = 0 := by 
        linarith [h02, h] 
      simp [ha]
    | inr h0 =>
      have h01 : f 2017 * f 2017 = f (2017 - 2017) := hf 2017 2017
      have h02 : f (2017 - 2017) = f 0 := by 
        ring_nf 
      rw [h02, h0] at h01
      have h11 : f (2017 / 2) * f (2017 / 2) = f ((2017 / 2) - (2017 / 2)) := hf (2017 / 2) (2017 / 2)
      have h12 : f ((2017 / 2) - (2017 / 2)) = f 0 := by 
        ring_nf 
      rw [h12, h0] at h11 
      have h13 : f (2017 / 2) = 1 ∨ f (2017 / 2) = -1 := by 
        have h22 : f (2017 / 2) ^ 2 = 1 := by nlinarith 
        have h111 : f (2017 / 2) ^ 2 - 1 = 0 := by linarith 
        have h112 : (f (2017 / 2) - 1) * (f (2017 / 2) + 1) = 0 := by 
          nlinarith 
        cases (mul_eq_zero.mp h112) with
        | inl h => 
          left 
          linarith 
        | inr h => 
          right 
          linarith 
      cases h13 with
      | inl h1111 =>
        -- f(2017/2) = 1, from f(2017) * f(2017/2) = f(2017/2)
        -- we get f(2017) = 1
        have h20 : f 2017 * f (2017 / 2) = f (2017 - (2017 / 2)) := hf 2017 (2017 / 2)
        have h22 : f (2017 - (2017 / 2)) = f (2017 / 2) := by 
          ring_nf 
        rw [h22] at h20 
        rw [h1111] at h20 
        have h21 : f 2017 = 1 := by 
          nlinarith 
        have ha : a = 1 := by 
          linarith [h21, h] 
        simp [ha] 
      | inr h1111 =>
        -- f(2017/2) = -1, from f(2017) * f(2017/2) = f(2017/2)
        -- we get f(2017) = 1
        have h20 : f 2017 * f (2017 / 2) = f (2017 - (2017 / 2)) := hf 2017 (2017 / 2)
        have h22 : f (2017 - (2017 / 2)) = f (2017 / 2) := by 
          ring_nf 
        rw [h22] at h20 
        rw [h1111] at h20 
        have h21 : f 2017 = 1 := by 
          nlinarith 
        have ha : a = 1 := by 
          linarith [h21, h] 
        simp [ha] 
  · -- exact {0,1}
    rintro (ha | ha)
    · -- 0
      use fun _ => (0 : ℝ)
      constructor 
      · -- funeq 
        intro x y 
        simp 
      · -- point 
        simp [ha] 
    · -- 1
      use fun _ => (1 : ℝ)
      constructor 
      · -- funeq 
        intro x y 
        simp 
      · -- point 
        simp [ha]