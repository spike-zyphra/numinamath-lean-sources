import Mathlib

-- Factorization of 48
lemma lemma_1 (a b : ℤ) (h : a * b = 48) :
    (a, b) = (1, 48) ∨ (a, b) = (2, 24) ∨ (a, b) = (3, 16) ∨ (a, b) = (4, 12) ∨
    (a, b) = (6, 8) ∨ (a, b) = (-1, -48) ∨ (a, b) = (-2, -24) ∨ (a, b) = (-3, -16) ∨
    (a, b) = (-4, -12) ∨ (a, b) = (-6, -8) ∨ (a, b) = (48, 1) ∨ (a, b) = (24, 2) ∨
    (a, b) = (16, 3) ∨ (a, b) = (12, 4) ∨ (a, b) = (8, 6) ∨ (a, b) = (-48, -1) ∨
    (a, b) = (-24, -2) ∨ (a, b) = (-16, -3) ∨ (a, b) = (-12, -4) ∨ (a, b) = (-8, -6) := by

  -- a divides 48
  have h1 : a ∣ 48 := by
    use b
    linarith

  have h2 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 ∨ a = -1 ∨ a = -2 ∨ a = -3 ∨ a = -4 ∨ a = -6 ∨ a = 48 ∨ a = 24 ∨ a = 16 ∨ a = 12 ∨ a = 8 ∨ a = -48 ∨ a = -24 ∨ a = -16 ∨ a = -12 ∨ a = -8 := by

    have h3 : a ≤ 48 := by
      apply Int.le_of_dvd (by norm_num) h1

    have h4 : a ≥ -48 := by
      have h5 : -a ∣ 48 := by
        exact Int.neg_dvd.2 h1
      have h6 : -a ≤ 48 := by
        apply Int.le_of_dvd (by norm_num) h5
      linarith

    interval_cases a <;> tauto

  rcases h2 with (r | r | r | r | r | r | r | r | r | r | r | r | r | r | r | r | r | r | r | r)

  · -- a = 1
    have hb : b = 48 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 2
    have hb : b = 24 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 3
    have hb : b = 16 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 4
    have hb : b = 12 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 6
    have hb : b = 8 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -1
    have hb : b = -48 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -2
    have hb : b = -24 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -3
    have hb : b = -16 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -4
    have hb : b = -12 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -6
    have hb : b = -8 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 48
    have hb : b = 1 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 24
    have hb : b = 2 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 16
    have hb : b = 3 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 12
    have hb : b = 4 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = 8
    have hb : b = 6 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -48
    have hb : b = -1 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -24
    have hb : b = -2 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -16
    have hb : b = -3 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -12
    have hb : b = -4 := by
      rw [r] at h
      linarith
    simp [r, hb]

  · -- a = -8
    have hb : b = -6 := by
      rw [r] at h
      linarith
    simp [r, hb]

set_option maxHeartbeats 200000000
theorem algebra_632102 :
  let set := {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y - 7 * x - 6 * y = 6 ∧ x < y};
  set.ncard = 5 :=
by
  intro set
  have : set
       = {(1+6,48+7), (2+6,24+7), (3+6,16+7), (4+6,12+7), (6+6,8+7)} := by
    simp [set]
    ext ⟨x,y⟩
    constructor; swap
    . intro h
      rcases h with (h|h|h|h|h) <;> rw [h] <;> simp
    . simp
      intro h1 h2 h3 h4
      --Eliminate the substraction.
      have : x*y = 7*x + 6*y + 6 := by
        have h3' := h3
        apply_fun (fun x => x + 6 * y) at h3
        rw [Nat.sub_add_cancel] at h3
        have h3'' := h3
        apply_fun (fun a => a + 7 * x) at h3
        rw [Nat.sub_add_cancel] at h3
        linarith
        have : ∀ a b : ℕ, a - b > 0 → a > b := by
          rintro a b h
          exact Nat.lt_of_sub_pos h
        . refine Nat.le_iff_lt_or_eq.mpr ?_
          left
          apply Nat.lt_of_sub_pos
          rw [h3'']
          simp
        . refine Nat.le_iff_lt_or_eq.mpr ?_
          left
          apply Nat.lt_of_sub_pos
          rw [h3']
          simp
      -- Firstly, note that we have $(x - 6) (y - 7) = 48$,
      -- so that we can show the goal by factorization.
      have mult : (x - 6 : ℤ) * (y - 7) = 48 := by
        zify at this
        ring_nf
        linarith
      -- Use the factorization lemma we have defined and process each cases.
      have H := lemma_1 _ _ mult
      rcases H with (H|H|H|H|H|H|H|H|H|H|H|H|H|H|H|H|H|H|H)
      . simp at H
        have : x = 7 ∧ y = 48+7 := by cases H; constructor <;> linarith
        rw [this.1, this.2]
        tauto
      . simp at H
        have : x = 8 ∧ y = 24 + 7 := by cases H; constructor <;> linarith
        rw [this.1, this.2]
        tauto
      . simp at H
        have : x = 9 ∧ y = 23 := by cases H; constructor <;> linarith
        rw [this.1, this.2]
        tauto
      . simp at H
        have : x = 10 ∧ y = 19 := by cases H; constructor <;> linarith
        rw [this.1, this.2]
        right; right; right; left
        tauto
      . simp at H
        have : x = 12 ∧ y = 15 := by cases H; constructor <;> omega
        rw [this.1, this.2]
        repeat right
        tauto
      . have : (y : ℤ) = -48 + 7 := by
          simp at H
          linarith
        simp at this
      . simp at H
        have : (y : ℤ) = -24 + 7 := by
          linarith
        simp at this
      . simp at H
        have : (y : ℤ) = -16 + 7 := by
          linarith
        simp at this
      . simp at H
        have : (y : ℤ) = -12 + 7 := by
          linarith
        simp at this
      . simp at H
        have : (y : ℤ) = -8 + 7 := by
          linarith
        simp at this
      . simp at H
        have : x = 48 + 6 ∧ y = 1 + 7 := by
          cases H; constructor <;> omega
        rw [this.1, this.2] at h4
        simp at h4
      . simp at H
        have : x = 24 + 6 ∧ y = 2 + 7 := by
          cases H; constructor <;> omega
        rw [this.1, this.2] at h4
        simp at h4
      . simp at H
        have : x = 16 + 6 ∧ y = 3 + 7 := by
          cases H; constructor <;> omega
        rw [this.1, this.2] at h4
        simp at h4
      . simp at H
        have : x = 12 + 6 ∧ y = 4 + 7 := by
          cases H; constructor <;> omega
        rw [this.1, this.2] at h4
        simp at h4
      . simp at H
        have : x = 8 + 6 ∧ y = 6 + 7 := by
          cases H; constructor <;> omega
        rw [this.1, this.2] at h4
        simp at h4
      . simp at H
        have : (x : ℤ) = - 48 + 6 := by
          omega
        simp at this
      . simp at H
        have : (x : ℤ) = - 18 := by
          omega
        simp at this
      . have : (x : ℤ) = - 10 := by
          simp at H;
          omega
        simp at this
      . have : (x : ℤ) = - 6 := by
          simp at H;
          omega
        simp at this
  rw [this]
  simp[Set.ncard, Set.encard]
